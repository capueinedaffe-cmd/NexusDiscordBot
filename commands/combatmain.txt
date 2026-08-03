"""
combat.py
---------
Sistema de combate NEXUS para Discord: por turnos, hasta 3 vs 3,
con HP, MANA, PH y las stats del sistema (FUE, RES, AGI).

Incluye Sistema de Ritmo de Batalla: combos que premian usar el mismo
tipo de acción consecutivamente, abriendo posibilidades tácticas.
"""

import time
import random
import discord
import json
with open("data/elements/elements.json", encoding="utf-8") as f:
    ELEMENTS_DATA = json.load(f)

from discord import app_commands
from discord.ext import tasks

from config import OWNER_ID
from store.characters_store import (
    get_character, get_user_characters, apply_level_penalty,
    get_character_transformations, record_combat_result
)
from store.abilities_store import get_ability, min_level_for, HABILIDADES
from store.equipment_store import get_equipment
from maths import combat_math as cmath
from maths.npc_ai_math import decidir_turno
from store.expedition_store import construir_personaje_enemigo, armar_oleadas_arpias, ARPIAS_POR_OLEADA
from session_guard import usuario_ocupado

TURN_TIMEOUT_SECONDS = 10 * 60   # 10 minutos
LOBBY_TIMEOUT_SECONDS = 5 * 60   # 5 minutos
MAX_PARTICIPANTS = 6             # 3 vs 3
TIPO_DANO_PUNOS = "contundente"  # Daño a puño limpio

# ── RITMO: Mapeo de elemento → estado alterado ──────────────────────
ESTADO_POR_ELEMENTO = {
    "radiacion":  {"nombre": "Quemadura",            "dano_turno": 6, "duracion": 3},
    "ion":        {"nombre": "Aturdimiento",          "dano_turno": 0, "duracion": 3},
    "nano":       {"nombre": "Empapado",              "dano_turno": 0, "duracion": 3},
    "cuantico":   {"nombre": "Congelación",           "dano_turno": 0, "duracion": 2},
    "terra":      {"nombre": "Petrificación",         "dano_turno": 0, "duracion": 2},
    "hadron":     {"nombre": "Desorientación",        "dano_turno": 0, "duracion": 3},
    "natura":     {"nombre": "Envenenado",            "dano_turno": 3, "duracion": 3},
    "mortis":     {"nombre": "Maldición",             "dano_turno": 0, "duracion": 3},
    "orden":      {"nombre": "Sellado",               "dano_turno": 0, "duracion": 2},
    "caos":       {"nombre": "Corrupción",            "dano_turno": 0, "duracion": 2},
    "mistico":    {"nombre": "Aturdimiento etéreo",   "dano_turno": 0, "duracion": 3},
    "cinetico":   {"nombre": "Inercia",               "dano_turno": 0, "duracion": 3},
}


async def owner_check(interaction: discord.Interaction) -> bool:
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message(
            "No tenés permiso para usar este comando.", ephemeral=True
        )
        return False
    return True


async def _publish(interaction: discord.Interaction, container, embed: discord.Embed):
    """
    Muestra el panel de estado (lobby o combate) editando el mensaje anterior
    si ya existe, en vez de mandar uno nuevo cada vez.
    """
    if container.status_message:
        try:
            await container.status_message.edit(embed=embed)
            return
        except discord.NotFound:
            pass

    container.status_message = await interaction.channel.send(embed=embed)


# ── Combatiente en vivo dentro de un combate ────────────────────────
class Fighter:
    def __init__(self, character, team, transformaciones=None):
        self.character = character
        self.owner_id = character.owner_id
        self.name = character.name
        self.is_npc = character.is_npc
        self.team = team

        self.vit_max = character.vit_max
        self.vit = character.vit_max
        self.mana_max = character.mana_max
        self.mana = character.mana_max
        self.fue = character.fue
        self.res = character.res
        self.agi = character.agi
        self.elemento = character.elemento
        self.level = character.level
        self.ph = 0  # se pisa abajo, queda así para no romper el orden de ph_max
        self.ph = self.ph_max
        self.is_defending = False
        self.escudo = None
        self.usos_habilidad_combate = 0

        self.distancia = 1

        self.arma_principal = get_equipment(character.equipo.get("arma_principal"))
        self.arma_secundaria = get_equipment(character.equipo.get("arma_secundaria"))
        self._piezas_armadura = [
            get_equipment(character.equipo.get("cabeza")),
            get_equipment(character.equipo.get("torso")),
            get_equipment(character.equipo.get("piernas")),
        ]
        self.armadura_combinada = cmath.combinar_defensas(self._piezas_armadura)

        self.transformaciones = {t["name"].lower(): t for t in (transformaciones or [])}
        self.transformado = False
        self.transformacion_activa = None
        self.elemento_vulnerable = None

        # ── RITMO: estructura de combo ──
        self.ritmo = {
            "tipo_ultima_accion": None,       # "ataque", "habilidad", "tecnica"
            "elemento_ultima_habilidad": None,
            "contador_ataques": 0,
            "contador_habilidades": 0,
            "contador_tecnicas": 0,
        }

        # ── RITMO: estados alterados ──
        self.estados = {}   # {nombre_estado: turnos_restantes}

    @property
    def peso_total(self):
        pesos = [self.arma_principal, self.arma_secundaria] + self._piezas_armadura
        return cmath.calcular_peso_total(p.get("peso") if p else None for p in pesos)

    @property
    def agi_efectiva(self):
        """AGI ya penalizada por estados, peso de arma(s) y armadura."""
        agi = self.agi
        # ── RITMO: Empapado reduce AGI a la mitad ──
        if "Empapado" in self.estados:
            agi = agi // 2
        return cmath.calcular_agi_efectiva(agi, self.peso_total, self.fue)

    # ── RITMO: métodos de ritmo ────────────────────────────────────
    def resetear_ritmo(self):
        """Reinicia todos los contadores de ritmo."""
        self.ritmo = {
            "tipo_ultima_accion": None,
            "elemento_ultima_habilidad": None,
            "contador_ataques": 0,
            "contador_habilidades": 0,
            "contador_tecnicas": 0,
        }

    def actualizar_ritmo_ataque(self):
        """Actualiza el track de ataques. Devuelve el nivel de combo (1-3)."""
        r = self.ritmo
        if r["tipo_ultima_accion"] == "ataque":
            r["contador_ataques"] += 1
        else:
            r["contador_ataques"] = 1
        # Resetear otros tracks
        r["contador_habilidades"] = 0
        r["contador_tecnicas"] = 0
        r["elemento_ultima_habilidad"] = None
        r["tipo_ultima_accion"] = "ataque"
        # El combo se reinicia a 1 si pasa de 3
        if r["contador_ataques"] > 3:
            r["contador_ataques"] = 1
        return r["contador_ataques"]

    def actualizar_ritmo_habilidad(self, elemento):
        """Actualiza el track de habilidades. Devuelve el nivel de combo (1-3)."""
        r = self.ritmo
        if r["tipo_ultima_accion"] == "habilidad" and r["elemento_ultima_habilidad"] == elemento:
            r["contador_habilidades"] += 1
        else:
            r["contador_habilidades"] = 1
        # Resetear otros tracks
        r["contador_ataques"] = 0
        r["contador_tecnicas"] = 0
        r["elemento_ultima_habilidad"] = elemento
        r["tipo_ultima_accion"] = "habilidad"
        # El combo se reinicia a 1 si pasa de 3
        if r["contador_habilidades"] > 3:
            r["contador_habilidades"] = 1
        return r["contador_habilidades"]

    def actualizar_ritmo_tecnica(self):
        """Actualiza el track de técnicas. Devuelve el nivel de combo (1-3)."""
        r = self.ritmo
        if r["tipo_ultima_accion"] == "tecnica":
            r["contador_tecnicas"] += 1
        else:
            r["contador_tecnicas"] = 1
        # Resetear otros tracks
        r["contador_ataques"] = 0
        r["contador_habilidades"] = 0
        r["elemento_ultima_habilidad"] = None
        r["tipo_ultima_accion"] = "tecnica"
        # El combo se reinicia a 1 si pasa de 3
        if r["contador_tecnicas"] > 3:
            r["contador_tecnicas"] = 1
        return r["contador_tecnicas"]

    def tiene_estado_bloqueante(self, accion):
        """
        Verifica si un estado alterado bloquea la acción indicada.
        Devuelve mensaje de error o None si no hay bloqueo.
        """
        if "Congelación" in self.estados and accion in ("atacar", "usar_tecnica", "moverse"):
            return f"❄️ **{self.name}** está congelado y no puede {accion.replace('_', ' ')}."
        if "Sellado" in self.estados and accion in ("usar_habilidad", "usar_tecnica"):
            return f"🔒 **{self.name}** está sellado y no puede usar habilidades/técnicas."
        if "Inercia" in self.estados and accion == "moverse":
            return f"🚫 **{self.name}** tiene Inercia y no puede moverse."
        if "Aturdimiento etéreo" in self.estados and accion == "transformar":
            return f"🌀 **{self.name}** tiene Aturdimiento etéreo y no puede transformarse."
        if "Petrificación" in self.estados and accion not in ("defender",):
            return f"🪨 **{self.name}** está petrificado. Solo puede defender."
        return None

    def procesar_estados(self):
        """
        Procesar estados alterados al inicio del turno.
        Aplica daño, reduce contadores, elimina expirados.
        Devuelve lista de mensajes.
        """
        mensajes = []
        expirados = []
        for estado, turnos in list(self.estados.items()):
            # Aplicar efectos de daño por turno
            if estado == "Quemadura":
                self.vit = max(0, self.vit - 6)
                mensajes.append(f"🔥 **{self.name}** sufre Quemadura (-6 HP)")
            elif estado == "Envenenado":
                self.vit = max(0, self.vit - 3)
                mensajes.append(f"☠️ **{self.name}** sufre Envenenamiento (-3 HP)")

            # Reducir duración
            self.estados[estado] = turnos - 1
            if self.estados[estado] <= 0:
                expirados.append(estado)
                mensajes.append(f"✅ **{self.name}** se recuperó de **{estado}**")

        for estado in expirados:
            del self.estados[estado]

        return mensajes

    def aplicar_estado(self, nombre_estado, duracion):
        """Aplica un estado alterado. Si ya lo tiene, renueva la duración."""
        self.estados[nombre_estado] = duracion

    # ── Fin métodos RITMO ──────────────────────────────────────────

    def activar_transformacion(self, trans):
        self.transformado = True
        self.transformacion_activa = trans

        self.vit_max += trans["stat_bonus_vit"]
        self.vit += trans["stat_bonus_vit"]
        self.mana_max += trans["stat_bonus_mana"]
        self.mana += trans["stat_bonus_mana"]
        self.fue += trans["stat_bonus_fue"]
        self.res += trans["stat_bonus_res"]
        self.agi += trans["stat_bonus_agi"]

        self.ph = min(self.ph_max, self.ph + 3)
        self.elemento_vulnerable = ELEMENTS_DATA["opuestos"].get(trans["element"])

    def desactivar_transformacion(self):
        trans = self.transformacion_activa
        self.vit_max -= trans["stat_bonus_vit"]
        self.vit = min(self.vit, self.vit_max)
        self.mana_max -= trans["stat_bonus_mana"]
        self.mana = max(0, min(self.mana, self.mana_max))
        self.fue -= trans["stat_bonus_fue"]
        self.res -= trans["stat_bonus_res"]
        self.agi -= trans["stat_bonus_agi"]

        self.transformado = False
        self.transformacion_activa = None
        self.ph = min(self.ph, self.ph_max)
        self.elemento_vulnerable = None

    def procesar_drain_transformacion(self):
        """Llamar al empezar el turno de este fighter. Devuelve un mensaje si la forma se rompió."""
        if not self.transformado:
            return None
        trans = self.transformacion_activa
        self.mana = max(0, self.mana - 1)
        self.ph = max(0, self.ph - trans["ph_drain_per_turn"])
        if self.mana <= 0:
            nombre = trans["name"]
            self.desactivar_transformacion()
            return f"💥 La transformación **{nombre}** de **{self.name}** se rompió al quedarse sin MANA."
        return None

    @property
    def ph_max(self):
        return 6 + (self.res // 3)

    @property
    def defense(self):
        return self.vit_max // 4

    @property
    def alive(self):
        return self.vit > 0

    def bar(self, current, maximum, length=10):
        filled = round((current / maximum) * length) if maximum > 0 else 0
        filled = max(0, min(length, filled))
        return "■" * filled + "□" * (length - filled)

    def status_line(self):
        # ── RITMO: mostrar estados alterados ──
        estados_str = ""
        if self.estados:
            estados_str = "\nEstados: " + ", ".join(
                f"{nombre} ({turnos}t)" for nombre, turnos in self.estados.items()
            )
        return (
            f"**{self.name}** (Equipo {self.team + 1}){' — 💀' if not self.alive else ''}\n"
            f"HP:   {self.bar(self.vit, self.vit_max)}  {self.vit}/{self.vit_max}\n"
            f"MANA: {self.bar(self.mana, self.mana_max)}  {self.mana}/{self.mana_max}\n"
            f"PH:   {self.bar(self.ph, self.ph_max)}  {self.ph}/{self.ph_max}\n"
            f"Distancia: {self.distancia}/5"
            f"{estados_str}"
        )


# ── Mecánica de esquiva ─────────────────────────────

def resolver_ataque(attacker, target, bono_stat, danio_base, elemento=None):
    """
    Resuelve esquiva → escudo elemental → Tirada de Grado → daño.
    Para HABILIDADES elementales puras (/usar_habilidad).
    Devuelve (texto_resultado, danio_infligido, evadido_bool).
    """
    # 1. Esquiva
    chance = cmath.calcular_esquiva(attacker.agi, target.agi)
    if random.randint(1, 100) <= chance:
        target.ph = min(target.ph_max, target.ph + 2)
        return (f"💨 **{target.name}** esquiva el ataque (+2 PH).", 0, True)

    # 2. Escudo elemental
    if elemento and target.escudo:
        eff = ELEMENTS_DATA["efectividad"].get(elemento, {}).get(target.escudo["elemento"], "neutral")
        necesarios = {"efectivo": 0, "neutral": 1, "no_efectivo": 2}[eff]
        if necesarios > 0:
            target.escudo["hits_taken"] += 1
            if target.escudo["hits_taken"] >= necesarios:
                texto = f"💥 El escudo **{target.escudo['nombre']}** se rompe, sin daño directo."
                target.escudo = None
            else:
                texto = f"🛡️ El escudo **{target.escudo['nombre']}** absorbe el golpe."
            return (texto, 0, False)
        else:
            target.escudo = None

    # 3. Tirada de Grado
    grado, total = cmath.tirar_grado(bono_stat)
    multiplicador = cmath.GRADO_MULTIPLICADOR[grado]

    # 4. Vulnerabilidad por transformación
    if elemento and target.elemento_vulnerable == elemento:
        multiplicador *= 1.5

    if target.is_defending:
        multiplicador *= 0.5
        target.is_defending = False

    damage = max(1, round(danio_base * multiplicador))

    # ── RITMO: Corrupción → daño recibido +100% ──
    if "Corrupción" in target.estados:
        damage = damage * 2

    # ── RITMO: Petrificación → DEF +20 fija ──
    if "Petrificación" in target.estados:
        damage = max(1, damage - 20)

    target.vit = max(0, target.vit - damage)

    etiquetas = {
        "fallo_parcial": "fallo parcial",
        "estandar": "éxito",
        "limpio": "éxito limpio",
        "critico": "¡CRÍTICO!",
    }
    texto = f"({etiquetas[grado]}, tirada {total}) **{damage}** de daño."
    return (texto, damage, False)


async def _resolver_turnos_npc(session):
    """
    Resuelve en cadena todos los turnos consecutivos de NPCs.
    Devuelve (texto_acumulado, combate_terminado_bool).
    """
    lineas = []
    terminado, msg_oleada = session.is_truly_over()
    if msg_oleada:
        lineas.append(msg_oleada)

    while not terminado and session.current.is_npc:
        npc = session.current

        # ── RITMO: procesar estados del NPC al inicio de su turno ──
        msgs_estados = npc.procesar_estados()
        lineas.extend(msgs_estados)
        if not npc.alive:
            terminado, msg_oleada = session.is_truly_over()
            if msg_oleada:
                lineas.append(msg_oleada)
            if terminado:
                break
            drain_msg = session.advance_turn()
            if drain_msg:
                lineas.append(drain_msg)
            terminado, msg_oleada = session.is_truly_over()
            if msg_oleada:
                lineas.append(msg_oleada)
            continue

        objetivos = [f for f in session.fighters if f.team != npc.team and f.alive]
        decision = decidir_turno(npc, objetivos)

        # ── RITMO: check de estados bloqueantes para NPCs ──
        if decision["accion"] == "atacar" and "Congelación" in npc.estados:
            decision = {"accion": "esperar"}
        if decision["accion"] == "mover" and ("Inercia" in npc.estados or "Congelación" in npc.estados):
            decision = {"accion": "esperar"}

        if decision["accion"] == "atacar":
            objetivo = decision["objetivo"]

            # ── RITMO: actualizar ritmo de ataque del NPC ──
            nivel_combo = npc.actualizar_ritmo_ataque()
            golpes_extra = max(0, nivel_combo - 1)

            golpes = cmath.calcular_ataques_basicos(npc.fue, npc.arma_principal, npc.arma_secundaria)
            guardia_restante = objetivo.is_defending
            for golpe in golpes:
                arma = golpe["arma"]
                tipo_dano = arma["tipo_dano"] if arma else TIPO_DANO_PUNOS
                fue_efectiva = golpe["fue_efectiva"]
                texto, danio, evadido = cmath.resolver_golpe_fisico(
                    bono_dado=fue_efectiva,
                    dano_base=fue_efectiva,
                    tipo_dano=tipo_dano,
                    agi_efectiva_atacante=npc.agi_efectiva,
                    agi_efectiva_defensor=objetivo.agi_efectiva,
                    armadura_defensor=objetivo.armadura_combinada,
                    vit_max_defensor=objetivo.vit_max,
                    defensor_en_guardia=guardia_restante,
                )
                guardia_restante = False
                # ── RITMO: Corrupción y Petrificación ──
                if "Corrupción" in objetivo.estados:
                    danio = danio * 2
                if "Petrificación" in objetivo.estados:
                    danio = max(1, danio - 20)
                objetivo.vit = max(0, objetivo.vit - danio)
                if evadido:
                    objetivo.ph = min(objetivo.ph_max, objetivo.ph + 2)
                else:
                    npc.ph = min(npc.ph_max, npc.ph + 2)
                nombre_arma = f" con **{arma['nombre']}**" if arma else ""
                lineas.append(f"🩸 **{npc.name}**{nombre_arma} → **{objetivo.name}**: {texto}")
                if not objetivo.alive:
                    break

            # ── RITMO: golpes extra del combo de ataque NPC ──
            for i in range(golpes_extra):
                if not objetivo.alive:
                    break
                arma = npc.arma_principal
                tipo_dano = arma["tipo_dano"] if arma else TIPO_DANO_PUNOS
                fue_efectiva = npc.fue
                texto, danio, evadido = cmath.resolver_golpe_fisico(
                    bono_dado=fue_efectiva,
                    dano_base=fue_efectiva,
                    tipo_dano=tipo_dano,
                    agi_efectiva_atacante=npc.agi_efectiva,
                    agi_efectiva_defensor=objetivo.agi_efectiva,
                    armadura_defensor=objetivo.armadura_combinada,
                    vit_max_defensor=objetivo.vit_max,
                    defensor_en_guardia=False,
                )
                if "Corrupción" in objetivo.estados:
                    danio = danio * 2
                if "Petrificación" in objetivo.estados:
                    danio = max(1, danio - 20)
                objetivo.vit = max(0, objetivo.vit - danio)
                if not evadido:
                    npc.ph = min(npc.ph_max, npc.ph + 2)
                nombre_arma = f" con **{arma['nombre']}**" if arma else ""
                combo_label = f" (Ritmo x{nivel_combo})" if i == 0 else ""
                lineas.append(f"⚔️ **{npc.name}**{nombre_arma} → **{objetivo.name}**: {texto}{combo_label}")
                if not objetivo.alive:
                    break

            objetivo.is_defending = False

        elif decision["accion"] == "mover":
            pasos = cmath.pasos_movimiento(npc.agi_efectiva)
            distancia_anterior = npc.distancia
            if decision["direccion"] == "avanzar":
                npc.distancia = max(0, npc.distancia - pasos)
            else:
                npc.distancia = min(5, npc.distancia + pasos)
            # ── RITMO: moverse reinicia ritmo ──
            npc.resetear_ritmo()
            lineas.append(f"🏃 **{npc.name}** se reposiciona ({distancia_anterior} → {npc.distancia}).")

        else:  # "esperar"
            # ── RITMO: esperar reinicia ritmo ──
            npc.resetear_ritmo()
            lineas.append(f"⏳ **{npc.name}** no tiene objetivos, espera.")

        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            lineas.append(msg_oleada)
        if terminado:
            break

        drain_msg = session.advance_turn()
        if drain_msg:
            lineas.append(drain_msg)

        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            lineas.append(msg_oleada)

    return "\n".join(lineas), terminado


async def _avanzar_y_resolver_npcs(session):
    """
    Avanza el turno una vez, y si los siguientes son NPCs los resuelve en cadena.
    Devuelve (texto_acumulado, combate_terminado_bool).
    """
    lineas = []

    drain_msg = session.advance_turn()
    if drain_msg:
        lineas.append(drain_msg)

    # ── RITMO: procesar estados del nuevo fighter al inicio de su turno ──
    if session.current.alive:
        msgs_estados = session.current.procesar_estados()
        if msgs_estados:
            lineas.extend(msgs_estados)

    texto_npc, terminado = await _resolver_turnos_npc(session)
    if texto_npc:
        lineas.append(texto_npc)

    return "\n".join(lineas), terminado


# ── Lobby de espera antes de un combate ─────────────────────────────
class CombatLobby:
    def __init__(self, channel_id):
        self.channel_id = channel_id
        self.participants = []
        self.ready_votes = set()
        self.created_at = time.time()
        self.status_message = None

    def owner_ids(self):
        return set(c.owner_id for c, _ in self.participants)

    def team_count(self, team):
        return len([1 for c, t in self.participants if t == team])

    def has_character(self, character):
        return any(c is character for c, _ in self.participants)

    def add(self, character, team):
        self.participants.append([character, team])

    def set_team(self, character, team):
        for entry in self.participants:
            if entry[0] is character:
                entry[1] = team

    def is_expired(self):
        return (time.time() - self.created_at) > LOBBY_TIMEOUT_SECONDS

    def build_embed(self):
        team0 = [c.name for c, t in self.participants if t == 0]
        team1 = [c.name for c, t in self.participants if t == 1]

        embed = discord.Embed(
            title="⚔️ Preparación de combate",
            description=(
                f"**Equipo 1:** {', '.join(team0) if team0 else '—'}\n"
                f"**Equipo 2:** {', '.join(team1) if team1 else '—'}\n\n"
                f"Listos: {len(self.ready_votes)}/{len(self.owner_ids())} jugadores\n\n"
                f"Usá `/cambiar_equipo` para cambiar de bando y `/preparado` cuando estés listo.\n"
                f"El combate se cancela solo si no todos confirman en 5 minutos."
            ),
            color=discord.Color.orange(),
        )
        return embed


# ── Sesión de combate activo ─────────────────────────────────────────
class CombatSession:
    def __init__(self, channel_id, fighters, oleadas_enemigos=None, equipo_oleadas=None):
        self.channel_id = channel_id
        self.fighters = fighters
        self.turn_index = 0
        self.round_number = 1
        self.paused = False
        self.pause_votes = set()
        self.resume_votes = set()
        self.terminate_votes = set()
        self.surrender_votes = {0: set(), 1: set()}
        self.last_action_time = time.time()
        self.status_message = None

        self.oleadas_restantes = list(oleadas_enemigos) if oleadas_enemigos else []
        self.equipo_oleadas = equipo_oleadas
        self.oleada_actual = 1
        self.oleadas_totales = 1 + len(self.oleadas_restantes)
        self.enemigos_derrotados_total = 0
        self._muertos_ya_contados = set()

        self._roll_initiative()

    def _roll_initiative(self):
        rolls = [(random.randint(1, 6) + f.agi, f) for f in self.fighters]
        rolls.sort(key=lambda x: x[0], reverse=True)
        self.fighters = [f for _, f in rolls]
        self.initiative_log = [(f.name, r) for r, f in rolls]

    def owner_ids(self):
        return set(f.owner_id for f in self.fighters)

    def team_owner_ids(self, team):
        return set(f.owner_id for f in self.fighters if f.team == team)

    @property
    def current(self):
        return self.fighters[self.turn_index]

    def alive_targets_for(self, fighter):
        return [f for f in self.fighters if f.team != fighter.team and f.alive]

    def advance_turn(self):
        """Pasa el turno al siguiente combatiente vivo."""
        n = len(self.fighters)
        for _ in range(n):
            self.turn_index = (self.turn_index + 1) % n
            if self.turn_index == 0:
                self.round_number += 1
            if self.fighters[self.turn_index].alive:
                break
        self.last_action_time = time.time()
        return self.current.procesar_drain_transformacion()

    def team_alive(self, team):
        return any(f.alive for f in self.fighters if f.team == team)

    def is_over(self):
        return not self.team_alive(0) or not self.team_alive(1)

    def avanzar_oleada_si_corresponde(self):
        if self.equipo_oleadas is None:
            return None
        if self.team_alive(self.equipo_oleadas):
            return None
        if not self.oleadas_restantes:
            return None

        nuevos_derrotados = [
            f for f in self.fighters
            if f.team == self.equipo_oleadas and not f.alive and id(f) not in self._muertos_ya_contados
        ]
        for f in nuevos_derrotados:
            self._muertos_ya_contados.add(id(f))
        self.enemigos_derrotados_total += len(nuevos_derrotados)

        siguiente_ids = self.oleadas_restantes.pop(0)
        nuevos = [Fighter(construir_personaje_enemigo(eid), self.equipo_oleadas) for eid in siguiente_ids]
        self.fighters.extend(nuevos)
        self.oleada_actual += 1

        nombres = ", ".join(f.name for f in nuevos)
        return f"🌊 ¡Oleada {self.oleada_actual}/{self.oleadas_totales}! Aparecen: {nombres}."

    def is_truly_over(self):
        if not self.is_over():
            return False, None
        mensaje = self.avanzar_oleada_si_corresponde()
        if mensaje:
            return False, mensaje
        return True, None

    def winning_team(self):
        if self.team_alive(0) and not self.team_alive(1):
            return 0
        if self.team_alive(1) and not self.team_alive(0):
            return 1
        return None

    # ── RITMO: línea de ritmo para el embed ──
    @staticmethod
    def _build_ritmo_line(fighter):
        r = fighter.ritmo
        if r["tipo_ultima_accion"] == "ataque" and r["contador_ataques"] > 1:
            return f"🗡️ Ritmo de ataque: x{r['contador_ataques']} (+{max(0, r['contador_ataques']-1)} golpes)"
        elif r["tipo_ultima_accion"] == "habilidad" and r["contador_habilidades"] > 1:
            elemento = r["elemento_ultima_habilidad"] or "?"
            return f"✨ Ritmo [{elemento}]: x{r['contador_habilidades']}"
        elif r["tipo_ultima_accion"] == "tecnica" and r["contador_tecnicas"] > 1:
            return f"🌀 Ritmo de técnica: x{r['contador_tecnicas']}"
        return None

    def status_embed(self, title="Estado del combate"):
        lines = [f.status_line() for f in self.fighters]
        header = f"Ronda {self.round_number} — Turno de **{self.current.name}**"

        # ── RITMO: agregar línea de ritmo si aplica ──
        ritmo_line = self._build_ritmo_line(self.current)
        if ritmo_line:
            header += f"\n{ritmo_line}"

        embed = discord.Embed(
            title=title,
            description=(
                header + "\n\n"
                + "\n\n".join(lines)
            ),
            color=discord.Color.red() if not self.paused else discord.Color.light_grey(),
        )
        if self.paused:
            embed.set_footer(text="⏸️ Combate pausado")
        return embed

# ── Almacenamiento en memoria ────────────────────────────────────────
LOBBIES = {}
ACTIVE_COMBATS = {}
MAX_SESIONES_POR_CANAL = 3

_bot_ref = None


def _agregar_lobby(channel_id, lobby):
    LOBBIES.setdefault(channel_id, []).append(lobby)


def _quitar_lobby(channel_id, lobby):
    lista = LOBBIES.get(channel_id)
    if not lista:
        return
    if lobby in lista:
        lista.remove(lobby)
    if not lista:
        del LOBBIES[channel_id]


def _lobby_de_owner(channel_id, owner_id):
    for lobby in LOBBIES.get(channel_id, []):
        if owner_id in lobby.owner_ids():
            return lobby
    return None


def _agregar_combate(channel_id, session):
    ACTIVE_COMBATS.setdefault(channel_id, []).append(session)


def _quitar_combate(channel_id, session):
    lista = ACTIVE_COMBATS.get(channel_id)
    if not lista:
        return
    if session in lista:
        lista.remove(session)
    if not lista:
        del ACTIVE_COMBATS[channel_id]


def _combate_de_owner(channel_id, owner_id):
    for session in ACTIVE_COMBATS.get(channel_id, []):
        if owner_id in session.owner_ids():
            return session
    return None


# ── Vista con el botón Reanudar ──────────────────────────────────────
class ResumeView(discord.ui.View):
    def __init__(self, session):
        super().__init__(timeout=None)
        self.session = session

    @discord.ui.button(label="Reanudar", style=discord.ButtonStyle.success, emoji="▶️")
    async def resume(self, interaction: discord.Interaction, button: discord.ui.Button):
        session = self.session
        if session not in ACTIVE_COMBATS.get(session.channel_id, []):
            await interaction.response.send_message("Este combate ya no existe.", ephemeral=True)
            return
        if interaction.user.id not in session.owner_ids():
            await interaction.response.send_message("No participás en este combate.", ephemeral=True)
            return

        session.resume_votes.add(interaction.user.id)
        needed = session.owner_ids()

        if session.resume_votes >= needed:
            session.paused = False
            session.resume_votes.clear()
            session.last_action_time = time.time()
            for child in self.children:
                child.disabled = True
            await interaction.response.edit_message(
                content="▶️ **Combate reanudado.**", view=self
            )
        else:
            await interaction.response.send_message(
                f"Voto para reanudar registrado ({len(session.resume_votes)}/{len(needed)}).",
                ephemeral=True,
            )


# ── RITMO: Vista para acción extra tras técnica combo ────────────────
class AccionExtraView(discord.ui.View):
    """
    Vista efímera con dos botones que aparece tras una técnica de
    combo nivel 2 o 3, ofreciendo al jugador una acción extra.
    Timeout: 30 segundos → si no elige, se avanza el turno sin extra.
    """

    def __init__(self, session, fighter, target, hab_data=None):
        super().__init__(timeout=30)
        self.session = session
        self.fighter = fighter
        self.target = target
        self.hab_data = hab_data
        self.resolved = False

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        return interaction.user.id == self.fighter.owner_id

    @discord.ui.button(label="⚔️ Ataque extra", style=discord.ButtonStyle.primary)
    async def btn_ataque_extra(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.resolved:
            return
        self.resolved = True
        self.stop()

        await interaction.response.defer(ephemeral=True)

        attacker = self.fighter
        target = self.target

        if not target.alive:
            vivos = [f for f in self.session.fighters if f.team != attacker.team and f.alive]
            if not vivos:
                await self._avanzar_y_publicar(interaction, "⚔️ No hay objetivos vivos para el ataque extra.")
                return
            target = vivos[0]

        if not cmath.puede_atacar(attacker.arma_principal, attacker.distancia):
            await self._avanzar_y_publicar(interaction, "⚔️ Distancia incorrecta para ataque extra.")
            return

        golpes = cmath.calcular_ataques_basicos(attacker.fue, attacker.arma_principal, attacker.arma_secundaria)
        lineas = []
        guardia = target.is_defending
        for golpe in golpes:
            arma = golpe["arma"]
            tipo_dano = arma["tipo_dano"] if arma else TIPO_DANO_PUNOS
            fue_ef = golpe["fue_efectiva"]
            texto, danio, evadido = cmath.resolver_golpe_fisico(
                bono_dado=fue_ef, dano_base=fue_ef, tipo_dano=tipo_dano,
                agi_efectiva_atacante=attacker.agi_efectiva,
                agi_efectiva_defensor=target.agi_efectiva,
                armadura_defensor=target.armadura_combinada,
                vit_max_defensor=target.vit_max,
                defensor_en_guardia=guardia,
            )
            guardia = False
            if "Corrupción" in target.estados:
                danio = danio * 2
            if "Petrificación" in target.estados:
                danio = max(1, danio - 20)
            target.vit = max(0, target.vit - danio)
            if evadido:
                target.ph = min(target.ph_max, target.ph + 2)
            else:
                attacker.ph = min(attacker.ph_max, attacker.ph + 2)
            nombre_arma = f" con **{arma['nombre']}**" if arma else ""
            lineas.append(f"⚔️ **{attacker.name}**{nombre_arma} → **{target.name}**: {texto}")
            if not target.alive:
                break
        target.is_defending = False

        resultado = "\n".join(lineas)
        await self._avanzar_y_publicar(interaction, resultado)

    @discord.ui.button(label="🌀 Técnica extra", style=discord.ButtonStyle.secondary)
    async def btn_tecnica_extra(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.resolved:
            return
        self.resolved = True
        self.stop()

        opciones = []
        for hab_id, hab in HABILIDADES.items():
            if hab.get("tipo") != "tecnica":
                continue
            if hab["elemento"] != self.fighter.elemento:
                continue
            if self.fighter.level < min_level_for(hab["tier"]):
                continue
            if hab.get("exclusiva_transformacion"):
                continue
            coste = hab.get("coste_pt", 0)
            opciones.append(discord.SelectOption(
                label=hab["nombre"],
                value=hab_id,
                description=f"Coste: {coste} PT"
            ))

        if not opciones:
            await interaction.response.defer(ephemeral=True)
            await self._avanzar_y_publicar(interaction, "🌀 No tenés técnicas disponibles para la acción extra.")
            return

        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(view=self)

        select_view = TecnicaExtraSelectView(
            self.session, self.fighter, self.target, opciones
        )
        await interaction.followup.send(
            "Elegí la técnica extra (coste normal, no acumula ritmo):",
            view=select_view, ephemeral=True
        )

    async def on_timeout(self):
        if self.resolved:
            return
        self.resolved = True
        await self._avanzar_sin_interaccion()

    async def _avanzar_y_publicar(self, interaction, resultado_extra):
        session = self.session

        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            resultado_extra += f"\n\n{msg_oleada}"
        if terminado:
            await _end_combat_victory(interaction, session, resultado_extra)
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = resultado_extra + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        try:
            await interaction.followup.send("Acción extra registrada.", ephemeral=True)
        except Exception:
            pass
        channel = _bot_ref.get_channel(session.channel_id)
        if channel and session.status_message:
            try:
                await session.status_message.edit(embed=embed)
            except discord.NotFound:
                session.status_message = await channel.send(embed=embed)

    async def _avanzar_sin_interaccion(self):
        session = self.session
        channel = _bot_ref.get_channel(session.channel_id)
        if not channel:
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto = "⏰ Tiempo agotado para la acción extra." + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            winning_team = session.winning_team()
            ganadores = [f.name for f in session.fighters if f.team == winning_team]
            embed = session.status_embed(title="🏆 Combate finalizado")
            embed.description = texto + f"\n\n**Equipo {winning_team + 1} gana!** ({', '.join(ganadores)})"
            if session.status_message:
                try:
                    await session.status_message.edit(embed=embed)
                except discord.NotFound:
                    session.status_message = await channel.send(embed=embed)
            else:
                session.status_message = await channel.send(embed=embed)
            await _persist_combat_stats(session, {winning_team: "victoria", 1 - winning_team: "derrota"})
            _quitar_combate(session.channel_id, session)
            return

        embed = session.status_embed()
        embed.description = texto + "\n\n" + embed.description
        if session.status_message:
            try:
                await session.status_message.edit(embed=embed)
            except discord.NotFound:
                session.status_message = await channel.send(embed=embed)
        else:
            session.status_message = await channel.send(embed=embed)


class TecnicaExtraSelectView(discord.ui.View):
    """Select menu para elegir la técnica extra (tras clic en 'Técnica extra')."""

    def __init__(self, session, fighter, target, opciones):
        super().__init__(timeout=30)
        self.session = session
        self.fighter = fighter
        self.target = target
        self.resolved = False

        self.select_menu = discord.ui.Select(
            placeholder="Elegí una técnica...",
            options=opciones[:25],
        )
        self.select_menu.callback = self._on_select
        self.add_item(self.select_menu)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        return interaction.user.id == self.fighter.owner_id

    async def _on_select(self, interaction: discord.Interaction):
        if self.resolved:
            return
        self.resolved = True
        self.stop()

        hab_id = self.select_menu.values[0]
        hab = HABILIDADES.get(hab_id)
        if not hab:
            await interaction.response.send_message("Técnica no encontrada.", ephemeral=True)
            await self._avanzar_y_publicar(interaction, "🌀 Técnica no encontrada.")
            return

        attacker = self.fighter
        target = self.target

        coste_pt = hab.get("coste_pt", 0)
        coste_mana = hab.get("costo_mana", 0)

        if attacker.ph < coste_pt or attacker.mana < coste_mana:
            await interaction.response.send_message(
                f"No tenés recursos para **{hab['nombre']}** (necesitás {coste_pt} PT, {coste_mana} MANA).",
                ephemeral=True,
            )
            await self._avanzar_y_publicar(interaction, f"🌀 **{attacker.name}** no tiene recursos para la técnica extra.")
            return

        attacker.ph -= coste_pt
        attacker.mana -= coste_mana

        rango = hab.get("rango", "cuerpo_a_cuerpo")
        if rango == "cuerpo_a_cuerpo" and attacker.distancia > 1:
            await self._avanzar_y_publicar(interaction, f"🌀 **{hab['nombre']}** requiere cuerpo a cuerpo.")
            return
        if rango == "distancia" and attacker.distancia < 2:
            await self._avanzar_y_publicar(interaction, f"🌀 **{hab['nombre']}** requiere distancia.")
            return

        fue_ef = cmath.fue_efectiva_tecnica(attacker.fue, attacker.arma_principal, attacker.arma_secundaria)
        tipo_fisico = hab.get("tipo_fisico")
        dano_fisico, _ = cmath.aplicar_penalizacion_tecnica(
            fue_ef, hab.get("modificador_dano", 0), coste_pt, attacker.arma_principal, tipo_fisico
        )
        tipo_dano = tipo_fisico or TIPO_DANO_PUNOS

        if not target.alive:
            vivos = [f for f in self.session.fighters if f.team != attacker.team and f.alive]
            if not vivos:
                await self._avanzar_y_publicar(interaction, "🌀 No hay objetivos vivos.")
                return
            target = vivos[0]

        texto, danio, evadido = cmath.resolver_golpe_fisico(
            bono_dado=fue_ef,
            dano_base=dano_fisico,
            tipo_dano=tipo_dano,
            agi_efectiva_atacante=attacker.agi_efectiva,
            agi_efectiva_defensor=target.agi_efectiva,
            armadura_defensor=target.armadura_combinada,
            vit_max_defensor=target.vit_max,
            defensor_en_guardia=target.is_defending,
        )
        if "Corrupción" in target.estados:
            danio = danio * 2
        if "Petrificación" in target.estados:
            danio = max(1, danio - 20)
        target.vit = max(0, target.vit - danio)
        target.is_defending = False

        resultado = f"🌀 **{attacker.name}** usa **{hab['nombre']}** → **{target.name}**: {texto}"
        await interaction.response.defer(ephemeral=True)
        await self._avanzar_y_publicar(interaction, resultado)

    async def on_timeout(self):
        if self.resolved:
            return
        self.resolved = True
        await self._avanzar_sin_interaccion()

    async def _avanzar_y_publicar(self, interaction, resultado_extra):
        session = self.session
        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            resultado_extra += f"\n\n{msg_oleada}"
        if terminado:
            await _end_combat_victory(interaction, session, resultado_extra)
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = resultado_extra + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        try:
            await interaction.followup.send("Técnica extra registrada.", ephemeral=True)
        except Exception:
            pass
        channel = _bot_ref.get_channel(session.channel_id)
        if channel and session.status_message:
            try:
                await session.status_message.edit(embed=embed)
            except discord.NotFound:
                session.status_message = await channel.send(embed=embed)

    async def _avanzar_sin_interaccion(self):
        session = self.session
        channel = _bot_ref.get_channel(session.channel_id)
        if not channel:
            return
        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto = "⏰ Tiempo agotado para elegir técnica extra." + (f"\n\n{npc_texto}" if npc_texto else "")
        if combate_termino:
            winning_team = session.winning_team()
            ganadores = [f.name for f in session.fighters if f.team == winning_team]
            embed = session.status_embed(title="🏆 Combate finalizado")
            embed.description = texto + f"\n\n**Equipo {winning_team + 1} gana!** ({', '.join(ganadores)})"
            if session.status_message:
                try:
                    await session.status_message.edit(embed=embed)
                except discord.NotFound:
                    session.status_message = await channel.send(embed=embed)
            else:
                session.status_message = await channel.send(embed=embed)
            await _persist_combat_stats(session, {winning_team: "victoria", 1 - winning_team: "derrota"})
            _quitar_combate(session.channel_id, session)
            return
        embed = session.status_embed()
        embed.description = texto + "\n\n" + embed.description
        if session.status_message:
            try:
                await session.status_message.edit(embed=embed)
            except discord.NotFound:
                session.status_message = await channel.send(embed=embed)
        else:
            session.status_message = await channel.send(embed=embed)


# ── Autocompletado ───────────────────────────────────────────────────
async def personaje_autocomplete(interaction: discord.Interaction, current: str):
    session = _combate_de_owner(interaction.channel_id, interaction.user.id)
    if not session:
        return []
    opts = [f for f in session.fighters if f.owner_id == interaction.user.id]
    return [
        app_commands.Choice(name=f.name, value=f.name)
        for f in opts if current.lower() in f.name.lower()
    ][:25]


async def objetivo_autocomplete(interaction: discord.Interaction, current: str):
    try:
        session = _combate_de_owner(interaction.channel_id, interaction.user.id)
        if not session:
            return []
        current_lower = (current or "").lower()
        opts = [f for f in session.fighters if f.alive]
        choices = []
        for f in opts:
            if current_lower in f.name.lower():
                choices.append(app_commands.Choice(
                    name=f"{f.name} (Equipo {f.team + 1})",
                    value=f.name
                ))
        return choices[:25]
    except Exception as e:
        print(f"[ERROR objetivo_autocomplete] {type(e).__name__}: {e}")
        return []


async def transformacion_autocomplete(interaction: discord.Interaction, current: str):
    session = _combate_de_owner(interaction.channel_id, interaction.user.id)
    if not session:
        return []
    nombre_personaje = interaction.namespace.personaje
    fighter = next(
        (f for f in session.fighters
         if f.owner_id == interaction.user.id
         and (not nombre_personaje or f.name.lower() == nombre_personaje.lower())),
        None,
    )
    if not fighter:
        return []
    return [
        app_commands.Choice(name=t["name"], value=t["name"])
        for t in fighter.transformaciones.values()
        if current.lower() in t["name"].lower()
    ][:25]


async def habilidad_autocomplete(interaction: discord.Interaction, current: str):
    session = _combate_de_owner(interaction.channel_id, interaction.user.id)
    if not session:
        return []
    nombre_personaje = interaction.namespace.personaje
    fighter = next(
        (f for f in session.fighters
         if f.owner_id == interaction.user.id
         and (not nombre_personaje or f.name.lower() == nombre_personaje.lower())),
        None,
    )
    if not fighter:
        return []

    opciones = []
    for hab_id, hab in HABILIDADES.items():
        if hab.get("tipo") == "tecnica":
            continue
        if hab["elemento"] != fighter.elemento:
            continue
        if hab.get("exclusiva_transformacion"):
            continue
        if fighter.level < min_level_for(hab["tier"]):
            continue
        if current.lower() in hab["nombre"].lower():
            opciones.append(app_commands.Choice(name=hab["nombre"], value=hab_id))
    return opciones[:25]


async def tecnica_autocomplete(interaction: discord.Interaction, current: str):
    session = _combate_de_owner(interaction.channel_id, interaction.user.id)
    if not session:
        return []
    nombre_personaje = interaction.namespace.personaje
    fighter = next(
        (f for f in session.fighters
         if f.owner_id == interaction.user.id
         and (not nombre_personaje or f.name.lower() == nombre_personaje.lower())),
        None,
    )
    if not fighter:
        return []

    opciones = []
    for hab_id, hab in HABILIDADES.items():
        if hab.get("tipo") != "tecnica":
            continue
        if hab["elemento"] != fighter.elemento:
            continue
        if hab.get("exclusiva_transformacion"):
            continue
        if fighter.level < min_level_for(hab["tier"]):
            continue
        if current.lower() in hab["nombre"].lower():
            opciones.append(app_commands.Choice(name=hab["nombre"], value=hab_id))
    return opciones[:25]


async def mi_personaje_lobby_autocomplete(interaction: discord.Interaction, current: str):
    chars = await get_user_characters(interaction.user.id, include_npc=True)
    return [
        app_commands.Choice(name=c.name, value=c.name)
        for c in chars if current.lower() in c.name.lower()
    ][:25]


# ── Funciones auxiliares de fin de combate ───────────────────────────
async def _end_combat_victory(interaction, session, result_line):
    """Finaliza el combate con victoria de un equipo."""
    winning_team = session.winning_team()
    if winning_team is None:
        embed = session.status_embed(title="⚔️ Combate finalizado — Empate")
        embed.description = result_line + "\n\n**Empate!**"
    else:
        ganadores = [f.name for f in session.fighters if f.team == winning_team and f.alive]
        embed = session.status_embed(title="🏆 Combate finalizado")
        embed.description = result_line + f"\n\n**Equipo {winning_team + 1} gana!** ({', '.join(ganadores)})"

    if session.status_message:
        try:
            await session.status_message.edit(embed=embed)
        except discord.NotFound:
            session.status_message = await interaction.channel.send(embed=embed)
    else:
        session.status_message = await interaction.channel.send(embed=embed)

    if winning_team is not None:
        results = {winning_team: "victoria", 1 - winning_team: "derrota"}
    else:
        results = {0: "empate", 1: "empate"}
    await _persist_combat_stats(session, results)
    _quitar_combate(session.channel_id, session)


async def _persist_combat_stats(session, results):
    """Registra los resultados del combate para cada personaje."""
    for fighter in session.fighters:
        if fighter.is_npc:
            continue
        result = results.get(fighter.team, "derrota")
        try:
            await record_combat_result(fighter.character, result)
        except Exception as e:
            print(f"[ERROR] No se pudo registrar resultado para {fighter.name}: {e}")

# ===== END combat2.py =====


# ===== BEGIN combat3.py =====

# ── Registro de comandos ───────────────────────────────────────────
def setup_combat_commands(bot):
    global _bot_ref
    _bot_ref = bot

    # ── /iniciar_combate ─────────────────────────────────────────
    @bot.tree.command(name="iniciar_combate", description="Crea o une un personaje a la sala de espera de combate (hasta 3 vs 3)")
    @app_commands.describe(
        personaje="Tu personaje a convocar",
        personaje2="[Solo owner] Segundo personaje a convocar",
        personaje3="[Solo owner] Tercer personaje a convocar",
    )
    @app_commands.autocomplete(
        personaje=mi_personaje_lobby_autocomplete,
        personaje2=mi_personaje_lobby_autocomplete,
        personaje3=mi_personaje_lobby_autocomplete,
    )
    async def iniciar_combate(interaction: discord.Interaction, personaje: str,
                               personaje2: str = None, personaje3: str = None):
        if await usuario_ocupado(interaction.user.id):
            await interaction.response.send_message(
                "Ya estás en un combate o expedición activa. No podés iniciar otro.", ephemeral=True
            )
            return

        lobbies_actuales = LOBBIES.get(interaction.channel_id, [])
        combates_actuales = ACTIVE_COMBATS.get(interaction.channel_id, [])
        mi_lobby = _lobby_de_owner(interaction.channel_id, interaction.user.id)

        if not mi_lobby and len(lobbies_actuales) >= MAX_SESIONES_POR_CANAL:
            await interaction.response.send_message(
                f"Ya hay {MAX_SESIONES_POR_CANAL} lobbies de combate preparándose en este canal.",
                ephemeral=True,
            )
            return

        if len(combates_actuales) >= MAX_SESIONES_POR_CANAL and not mi_lobby:
            await interaction.response.send_message(
                f"Ya hay {MAX_SESIONES_POR_CANAL} combates activos en este canal.", ephemeral=True
            )
            return

        nombres_pedidos = [n for n in (personaje, personaje2, personaje3) if n]

        if len(nombres_pedidos) > 1 and interaction.user.id != OWNER_ID:
            await interaction.response.send_message(
                "Solo el anfitrión puede convocar más de un personaje a la vez.",
                ephemeral=True,
            )
            return

        characters = []
        for nombre in nombres_pedidos:
            char = await get_character(interaction.user.id, nombre)
            if not char:
                await interaction.response.send_message(
                    f"No tenés un personaje llamado **{nombre}**.", ephemeral=True
                )
                return
            characters.append(char)

        lobby = mi_lobby
        if lobby is None:
            lobby = CombatLobby(interaction.channel_id)
            _agregar_lobby(interaction.channel_id, lobby)

        for char in characters:
            if lobby.has_character(char):
                continue
            if len(lobby.participants) >= MAX_PARTICIPANTS:
                await interaction.response.send_message(
                    "El combate ya tiene el máximo de 6 participantes.", ephemeral=True
                )
                return
            team = 0 if lobby.team_count(0) <= lobby.team_count(1) else 1
            lobby.add(char, team)

        await interaction.response.send_message("Te uniste al combate.", ephemeral=True)
        await _publish(interaction, lobby, lobby.build_embed())

    # ── /cambiar_equipo ──────────────────────────────────────────
    @bot.tree.command(name="cambiar_equipo", description="Cambia de equipo dentro de la sala de espera")
    @app_commands.describe(personaje="Personaje a mover (si no lo indicás, se mueven todos los tuyos)")
    @app_commands.autocomplete(personaje=mi_personaje_lobby_autocomplete)
    async def cambiar_equipo(interaction: discord.Interaction, personaje: str = None):
        lobby = LOBBIES.get(interaction.channel_id)
        if not lobby:
            await interaction.response.send_message("No hay ningún combate en preparación aquí.", ephemeral=True)
            return

        mis_entradas = [e for e in lobby.participants if e[0].owner_id == interaction.user.id]
        if not mis_entradas:
            await interaction.response.send_message("No tenés personajes en esta sala de espera.", ephemeral=True)
            return

        if personaje:
            objetivo = [e for e in mis_entradas if e[0].name.lower() == personaje.lower()]
            if not objetivo:
                await interaction.response.send_message(f"No encontré a **{personaje}** en la sala.", ephemeral=True)
                return
            entradas_a_mover = objetivo
        else:
            entradas_a_mover = mis_entradas

        for entrada in entradas_a_mover:
            entrada[1] = 1 - entrada[1]

        await interaction.response.send_message("Cambiaste de equipo.", ephemeral=True)
        await _publish(interaction, lobby, lobby.build_embed())

    # ── /preparado ───────────────────────────────────────────────
    @bot.tree.command(name="preparado", description="Marca que estás listo para empezar el combate")
    async def preparado(interaction: discord.Interaction):
        lobby = LOBBIES.get(interaction.channel_id)
        if not lobby:
            await interaction.response.send_message("No hay ningún combate en preparación aquí.", ephemeral=True)
            return

        if interaction.user.id not in lobby.owner_ids():
            await interaction.response.send_message("No tenés personajes en esta sala de espera.", ephemeral=True)
            return

        lobby.ready_votes.add(interaction.user.id)

        if len(lobby.participants) < 2:
            await interaction.response.send_message(
                "No se puede iniciar un combate con un solo participante.", ephemeral=True
            )
            return

        if lobby.ready_votes >= lobby.owner_ids():
            fighters = []
            for char, team in lobby.participants:
                trans_rows = await get_character_transformations(char.id)
                fighters.append(Fighter(char, team, transformaciones=trans_rows))
            session = CombatSession(interaction.channel_id, fighters)
            _agregar_combate(interaction.channel_id, session)
            _quitar_lobby(interaction.channel_id, lobby)

            init_text = "\n".join(f"{name}: {roll}" for name, roll in session.initiative_log)

            texto_npc_inicial, combate_termino_de_una = await _resolver_turnos_npc(session)

            embed = session.status_embed(title="⚔️ ¡Combate iniciado!")
            embed.add_field(name="Iniciativa (1d6 + AGI)", value=init_text, inline=False)
            if texto_npc_inicial:
                embed.description = texto_npc_inicial + "\n\n" + embed.description

            await interaction.response.send_message("¡Todos listos! El combate comienza.", ephemeral=True)

            if combate_termino_de_una:
                winning_team = session.winning_team()
                ganadores = [f.name for f in session.fighters if f.team == winning_team]
                embed.title = "🏆 Combate finalizado"
                embed.description += f"\n\n**Equipo {winning_team + 1} gana!** ({', '.join(ganadores)})"
                session.status_message = await interaction.channel.send(embed=embed)
                await _persist_combat_stats(session, {winning_team: "victoria", 1 - winning_team: "derrota"})
                _quitar_combate(interaction.channel_id, session)
            else:
                session.status_message = await interaction.channel.send(embed=embed)
        else:
            await interaction.response.send_message(
                f"Listo registrado ({len(lobby.ready_votes)}/{len(lobby.owner_ids())}).", ephemeral=True
            )
            await _publish(interaction, lobby, lobby.build_embed())

    # ── Helper interno de resolución de acción ──────────────────
    def _get_active_session(interaction):
        return _combate_de_owner(interaction.channel_id, interaction.user.id)

    def _validate_turn(session, interaction, personaje_nombre):
        """Devuelve (fighter, error_msg). Si error_msg no es None, abortar."""
        current = session.current
        if current.owner_id != interaction.user.id:
            return None, f"No es tu turno. Le toca a **{current.name}**."
        if current.name.lower() != personaje_nombre.lower():
            return None, f"En este momento actúa **{current.name}**, no {personaje_nombre}."
        return current, None

    # ── /atacar ──────────────────────────────────────────────────
    @bot.tree.command(name="atacar", description="Ataque básico con tu(s) arma(s) equipada(s), pasa el turno")
    @app_commands.describe(personaje="Tu personaje que ataca", objetivo="A quién atacás")
    @app_commands.autocomplete(personaje=personaje_autocomplete, objetivo=objetivo_autocomplete)
    async def atacar(interaction: discord.Interaction, personaje: str, objetivo: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        attacker, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: verificar estado bloqueante ──
        bloqueo = attacker.tiene_estado_bloqueante("atacar")
        if bloqueo:
            await interaction.response.send_message(bloqueo, ephemeral=True)
            return

        target = next((f for f in session.fighters if f.name.lower() == objetivo.lower() and f.alive), None)
        if not target or target.team == attacker.team:
            await interaction.response.send_message("Objetivo inválido.", ephemeral=True)
            return

        # ── RITMO: Desorientación — 25% chance de atacar aliado ──
        if "Desorientación" in attacker.estados:
            if random.randint(1, 100) <= 25:
                aliados_vivos = [f for f in session.fighters if f.team == attacker.team and f.alive and f is not attacker]
                if aliados_vivos:
                    target = random.choice(aliados_vivos)

        golpes = cmath.calcular_ataques_basicos(attacker.fue, attacker.arma_principal, attacker.arma_secundaria)

        # Verificar distancia
        for golpe in golpes:
            if not cmath.puede_atacar(golpe["arma"], attacker.distancia):
                nombre_arma = golpe["arma"]["nombre"] if golpe["arma"] else "tus puños"
                await interaction.response.send_message(
                    f"**{nombre_arma}** no puede atacar a distancia {attacker.distancia}. "
                    f"Turno perdido, usá `/moverse` primero.",
                    ephemeral=True,
                )
                # ── RITMO: distancia incorrecta pierde turno → reset ritmo ──
                attacker.resetear_ritmo()
                drain_msg = session.advance_turn()
                embed = session.status_embed()
                texto = f"❌ **{attacker.name}** falla su ataque: distancia incorrecta."
                embed.description = texto + (f"\n\n{drain_msg}" if drain_msg else "") + "\n\n" + embed.description
                await _publish(interaction, session, embed)
                return

        # ── RITMO: actualizar ritmo de ataque ──
        nivel_combo = attacker.actualizar_ritmo_ataque()
        golpes_extra = max(0, nivel_combo - 1)

        lineas_resultado = []

        # Indicar Desorientación si redirigió
        if "Desorientación" in attacker.estados and target.team == attacker.team:
            lineas_resultado.append(f"😵 **{attacker.name}** está desorientado y ataca a un aliado!")

        # Indicar combo si nivel > 1
        if nivel_combo > 1:
            lineas_resultado.append(f"🗡️ **Ritmo de ataque x{nivel_combo}** (+{golpes_extra} golpe(s) extra)")

        guardia_restante = target.is_defending
        for golpe in golpes:
            arma = golpe["arma"]
            tipo_dano = arma["tipo_dano"] if arma else TIPO_DANO_PUNOS
            fue_efectiva = golpe["fue_efectiva"]
            texto, danio, evadido = cmath.resolver_golpe_fisico(
                bono_dado=fue_efectiva,
                dano_base=fue_efectiva,
                tipo_dano=tipo_dano,
                agi_efectiva_atacante=attacker.agi_efectiva,
                agi_efectiva_defensor=target.agi_efectiva,
                armadura_defensor=target.armadura_combinada,
                vit_max_defensor=target.vit_max,
                defensor_en_guardia=guardia_restante,
            )
            guardia_restante = False
            # ── RITMO: Corrupción / Petrificación ──
            if "Corrupción" in target.estados:
                danio = danio * 2
            if "Petrificación" in target.estados:
                danio = max(1, danio - 20)
            target.vit = max(0, target.vit - danio)

            if evadido:
                target.ph = min(target.ph_max, target.ph + 2)
            else:
                ph_ganado = 2 + (1 if attacker.transformado else 0)
                attacker.ph = min(attacker.ph_max, attacker.ph + ph_ganado)

            nombre_arma = f" con **{arma['nombre']}**" if arma else ""
            lineas_resultado.append(f"⚔️ **{attacker.name}**{nombre_arma} → **{target.name}**: {texto}")

            if not target.alive:
                break

        # ── RITMO: resolver golpes extra del combo ──
        for i in range(golpes_extra):
            if not target.alive:
                break
            arma = attacker.arma_principal
            tipo_dano = arma["tipo_dano"] if arma else TIPO_DANO_PUNOS
            fue_efectiva = attacker.fue  # golpe extra con FUE completa
            texto, danio, evadido = cmath.resolver_golpe_fisico(
                bono_dado=fue_efectiva,
                dano_base=fue_efectiva,
                tipo_dano=tipo_dano,
                agi_efectiva_atacante=attacker.agi_efectiva,
                agi_efectiva_defensor=target.agi_efectiva,
                armadura_defensor=target.armadura_combinada,
                vit_max_defensor=target.vit_max,
                defensor_en_guardia=False,
            )
            # ── RITMO: Corrupción / Petrificación ──
            if "Corrupción" in target.estados:
                danio = danio * 2
            if "Petrificación" in target.estados:
                danio = max(1, danio - 20)
            target.vit = max(0, target.vit - danio)
            if not evadido:
                ph_ganado = 2 + (1 if attacker.transformado else 0)
                attacker.ph = min(attacker.ph_max, attacker.ph + ph_ganado)
            else:
                target.ph = min(target.ph_max, target.ph + 2)
            nombre_arma = f" con **{arma['nombre']}**" if arma else ""
            lineas_resultado.append(f"⚔️ **{attacker.name}**{nombre_arma} → **{target.name}**: {texto} *(golpe extra)*")
            if not target.alive:
                break

        target.is_defending = False
        result_line = "\n".join(lineas_resultado)

        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            result_line += f"\n\n{msg_oleada}"
        if terminado:
            await _end_combat_victory(interaction, session, result_line)
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /defender ────────────────────────────────────────────────
    @bot.tree.command(name="defender", description="Reduce el próximo golpe a la mitad (genera +1 PH), pasa el turno")
    @app_commands.describe(personaje="Tu personaje que se defiende")
    @app_commands.autocomplete(personaje=personaje_autocomplete)
    async def defender(interaction: discord.Interaction, personaje: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: defender reinicia todos los contadores ──
        fighter.resetear_ritmo()

        fighter.is_defending = True
        ph_ganado = 1 + (1 if fighter.transformado else 0)
        fighter.ph = min(fighter.ph_max, fighter.ph + ph_ganado)
        result_line = f"🛡️ **{fighter.name}** se pone en guardia. (+1 PH)"

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /moverse ─────────────────────────────────────────────────
    @bot.tree.command(name="moverse", description="Avanza o retrocede en distancia (consume el turno, no ataca)")
    @app_commands.describe(personaje="Tu personaje que se mueve", direccion="Acercarse o alejarse del rival")
    @app_commands.choices(direccion=[
        app_commands.Choice(name="Avanzar (acercarse)", value="avanzar"),
        app_commands.Choice(name="Retroceder (alejarse)", value="retroceder"),
    ])
    @app_commands.autocomplete(personaje=personaje_autocomplete)
    async def moverse(interaction: discord.Interaction, personaje: str, direccion: app_commands.Choice[str]):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: verificar estado bloqueante ──
        bloqueo = fighter.tiene_estado_bloqueante("moverse")
        if bloqueo:
            await interaction.response.send_message(bloqueo, ephemeral=True)
            return

        # ── RITMO: moverse reinicia todos los contadores ──
        fighter.resetear_ritmo()

        pasos = cmath.pasos_movimiento(fighter.agi_efectiva)
        distancia_anterior = fighter.distancia
        if direccion.value == "avanzar":
            fighter.distancia = max(0, fighter.distancia - pasos)
        else:
            fighter.distancia = min(5, fighter.distancia + pasos)

        result_line = (
            f"🏃 **{fighter.name}** {direccion.name.lower()} "
            f"({distancia_anterior} → {fighter.distancia}, {pasos} paso(s) según su AGI efectiva)."
        )

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /esperar ─────────────────────────────────────────────────
    @bot.tree.command(name="esperar", description="No hacés nada este turno")
    @app_commands.describe(personaje="Tu personaje que espera")
    @app_commands.autocomplete(personaje=personaje_autocomplete)
    async def esperar(interaction: discord.Interaction, personaje: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: esperar reinicia todos los contadores ──
        fighter.resetear_ritmo()

        result_line = f"⏳ **{fighter.name}** no hace nada."

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /usar_habilidad ──────────────────────────────────────────
    @bot.tree.command(name="usar_habilidad", description="Usa una habilidad de tu elemento, pasa el turno")
    @app_commands.describe(personaje="Tu personaje que actúa", habilidad="Habilidad a usar", objetivo="A quién ataca (no aplica en habilidades defensivas)")
    @app_commands.autocomplete(personaje=personaje_autocomplete, objetivo=objetivo_autocomplete, habilidad=habilidad_autocomplete)
    async def usar_habilidad(interaction: discord.Interaction, personaje: str, habilidad: str, objetivo: str = None):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: verificar estado bloqueante ──
        bloqueo = fighter.tiene_estado_bloqueante("usar_habilidad")
        if bloqueo:
            await interaction.response.send_message(bloqueo, ephemeral=True)
            return

        hab = HABILIDADES.get(habilidad)
        if not hab or hab.get("tipo") == "tecnica":
            await interaction.response.send_message("Habilidad no encontrada o es una técnica (usá /usar_tecnica).", ephemeral=True)
            return
        if hab["elemento"] != fighter.elemento:
            await interaction.response.send_message(f"Tu elemento es **{fighter.elemento}**, no podés usar **{hab['nombre']}**.", ephemeral=True)
            return
        if fighter.level < min_level_for(hab["tier"]):
            await interaction.response.send_message("Nivel insuficiente para esa habilidad.", ephemeral=True)
            return

        # ── RITMO: Calcular nivel de combo ──
        nivel_combo = fighter.actualizar_ritmo_habilidad(hab["elemento"])

        # Costes base
        coste_mana_base = hab.get("costo_mana", 0)
        coste_mana_extra = 0
        if nivel_combo == 2:
            coste_mana_extra = 1
        elif nivel_combo == 3:
            coste_mana_extra = 2

        coste_mana_total = coste_mana_base + coste_mana_extra

        # ── RITMO: Si no alcanza MANA para combo, ejecutar como nivel 1 ──
        if fighter.mana < coste_mana_total:
            nivel_combo = 1
            coste_mana_extra = 0
            coste_mana_total = coste_mana_base

        # Verificar MANA base
        if fighter.mana < coste_mana_base:
            await interaction.response.send_message(
                f"No tenés suficiente MANA ({fighter.mana}/{coste_mana_base}).", ephemeral=True
            )
            return

        # Deducir MANA
        fighter.mana -= coste_mana_total

        lineas_resultado = []

        # Indicar combo si nivel > 1
        if nivel_combo > 1:
            extra_texto = f" (+{coste_mana_extra} MANA de ritmo)" if coste_mana_extra > 0 else ""
            lineas_resultado.append(f"✨ **Ritmo [{hab['elemento']}] x{nivel_combo}**{extra_texto}")

        # ── RITMO: Maldición → no puede curarse ──
        if "Maldición" in fighter.estados and hab.get("tipo") == "ataque" and hab.get("modificador_dano", 0) < 0:
            lineas_resultado.append(f"😿 **{fighter.name}** tiene Maldición y no puede curarse.")

        # Resolución según tipo de habilidad
        if hab["tipo"] == "defensa":
            fighter.escudo = {
                "elemento": hab["elemento"],
                "nombre": hab["nombre"],
                "hits_taken": 0,
            }
            lineas_resultado.append(f"🛡️ **{fighter.name}** activa **{hab['nombre']}**.")
        else:
            # Habilidad de ataque
            if not objetivo:
                await interaction.response.send_message("Necesitás especificar un objetivo.", ephemeral=True)
                return

            target = next((f for f in session.fighters if f.name.lower() == objetivo.lower() and f.alive), None)
            if not target or target.team == fighter.team:
                await interaction.response.send_message("Objetivo inválido.", ephemeral=True)
                return

            bono_stat = fighter.fue if hab["elemento"] in ("radiacion", "hadron") else fighter.res
            danio_base = bono_stat + hab.get("modificador_dano", 0)

            # ── RITMO: Nivel 2 → +50% daño ──
            if nivel_combo == 2:
                danio_base = int(danio_base * 1.5)

            # ── RITMO: Nivel 3 → daño en área O estado alterado ──
            if nivel_combo == 3:
                if hab.get("es_area"):
                    # Aplicar estado alterado según el elemento
                    info_estado = ESTADO_POR_ELEMENTO.get(hab["elemento"])
                    if info_estado:
                        # Aplicar a todos los rivales vivos
                        rivales = [f for f in session.fighters if f.team != fighter.team and f.alive]
                        for rival in rivales:
                            rival.aplicar_estado(info_estado["nombre"], info_estado["duracion"])
                        lineas_resultado.append(
                            f"💥 **{hab['nombre']}** aplica **{info_estado['nombre']}** a todos los rivales!"
                        )
                else:
                    # Daño en área a todos los rivales vivos
                    rivales = [f for f in session.fighters if f.team != fighter.team and f.alive]
                    for rival in rivales:
                        texto, danio, evadido = resolver_ataque(fighter, rival, bono_stat, danio_base, hab["elemento"])
                        if not evadido:
                            pass  # el daño ya se aplicó dentro de resolver_ataque
                        lineas_resultado.append(f"✨ **{fighter.name}** → **{rival.name}**: {texto}")
                    target = None  # Ya se procesó todo
            else:
                # Ataque normal (nivel 1 o 2, un solo objetivo)
                texto, danio, evadido = resolver_ataque(fighter, target, bono_stat, danio_base, hab["elemento"])
                lineas_resultado.append(f"✨ **{fighter.name}** usa **{hab['nombre']}** → **{target.name}**: {texto}")
                target = None  # Ya se procesó

        fighter.usos_habilidad_combate += 1
        result_line = "\n".join(lineas_resultado)

        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            result_line += f"\n\n{msg_oleada}"
        if terminado:
            await _end_combat_victory(interaction, session, result_line)
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /usar_tecnica ────────────────────────────────────────────
    @bot.tree.command(name="usar_tecnica", description="Usa una técnica híbrida, pasa el turno")
    @app_commands.describe(personaje="Tu personaje que actúa", tecnica="Técnica a usar", objetivo="A quién ataca")
    @app_commands.autocomplete(personaje=personaje_autocomplete, objetivo=objetivo_autocomplete, tecnica=tecnica_autocomplete)
    async def usar_tecnica(interaction: discord.Interaction, personaje: str, tecnica: str, objetivo: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: verificar estado bloqueante ──
        bloqueo = fighter.tiene_estado_bloqueante("usar_tecnica")
        if bloqueo:
            await interaction.response.send_message(bloqueo, ephemeral=True)
            return

        hab = HABILIDADES.get(tecnica)
        if not hab or hab.get("tipo") != "tecnica":
            await interaction.response.send_message("Técnica no encontrada.", ephemeral=True)
            return
        if hab["elemento"] != fighter.elemento:
            await interaction.response.send_message(f"Tu elemento es **{fighter.elemento}**, no podés usar **{hab['nombre']}**.", ephemeral=True)
            return
        if fighter.level < min_level_for(hab["tier"]):
            await interaction.response.send_message("Nivel insuficiente para esa técnica.", ephemeral=True)
            return

        target = next((f for f in session.fighters if f.name.lower() == objetivo.lower() and f.alive), None)
        if not target or target.team == fighter.team:
            await interaction.response.send_message("Objetivo inválido.", ephemeral=True)
            return

        # ── RITMO: Calcular nivel de combo ──
        nivel_combo = fighter.actualizar_ritmo_tecnica()

        # Costes base
        coste_pt_base = hab.get("coste_pt", 0)
        coste_mana_base = hab.get("costo_mana", 0)

        # ── RITMO: Costes extra por combo ──
        coste_pt_extra = 0
        coste_mana_extra = 0
        permite_accion_extra = False
        tecnica_doble = False

        if nivel_combo == 2:
            coste_pt_extra = 1
            permite_accion_extra = True
        elif nivel_combo == 3:
            coste_pt_extra = 2
            coste_mana_extra = 1
            permite_accion_extra = True
            tecnica_doble = True

        coste_pt_total = coste_pt_base + coste_pt_extra
        coste_mana_total = coste_mana_base + coste_mana_extra

        # ── RITMO: Si no alcanzan recursos para combo, ejecutar como nivel 1 ──
        if fighter.ph < coste_pt_total or fighter.mana < coste_mana_total:
            nivel_combo = 1
            coste_pt_extra = 0
            coste_mana_extra = 0
            coste_pt_total = coste_pt_base
            coste_mana_total = coste_mana_base
            permite_accion_extra = False
            tecnica_doble = False

        # Verificar recursos base
        if fighter.ph < coste_pt_base or fighter.mana < coste_mana_base:
            await interaction.response.send_message(
                f"No tenés suficientes recursos (necesitás {coste_pt_base} PT, {coste_mana_base} MANA).",
                ephemeral=True
            )
            return

        # Deducir recursos
        fighter.ph -= coste_pt_total
        fighter.mana -= coste_mana_total

        # Verificar distancia según rango
        rango = hab.get("rango", "cuerpo_a_cuerpo")
        if rango == "cuerpo_a_cuerpo" and fighter.distancia > 1:
            await interaction.response.send_message(
                f"**{hab['nombre']}** solo se puede usar cuerpo a cuerpo. Usá `/moverse` primero.",
                ephemeral=True,
            )
            return
        if rango == "distancia" and fighter.distancia < 2:
            await interaction.response.send_message(
                f"**{hab['nombre']}** solo se puede usar a distancia. Usá `/moverse` primero.",
                ephemeral=True,
            )
            return

        # Resolver técnica
        fue_ef = cmath.fue_efectiva_tecnica(fighter.fue, fighter.arma_principal, fighter.arma_secundaria)
        tipo_fisico = hab.get("tipo_fisico")
        dano_fisico, _ = cmath.aplicar_penalizacion_tecnica(
            fue_ef, hab.get("modificador_dano", 0), coste_pt_base, fighter.arma_principal, tipo_fisico
        )
        tipo_dano = tipo_fisico or TIPO_DANO_PUNOS

        lineas_resultado = []

        # Indicar combo si nivel > 1
        if nivel_combo > 1:
            extra_pt = f" (+{coste_pt_extra} PT" if coste_pt_extra > 0 else ""
            extra_mana = f", +{coste_mana_extra} MANA" if coste_mana_extra > 0 else ""
            cierre = ")" if extra_pt or extra_mana else ""
            lineas_resultado.append(f"🌀 **Ritmo de técnica x{nivel_combo}**{extra_pt}{extra_mana}{cierre}")

        # Ejecutar técnica
        texto, danio, evadido = cmath.resolver_golpe_fisico(
            bono_dado=fue_ef,
            dano_base=dano_fisico,
            tipo_dano=tipo_dano,
            agi_efectiva_atacante=fighter.agi_efectiva,
            agi_efectiva_defensor=target.agi_efectiva,
            armadura_defensor=target.armadura_combinada,
            vit_max_defensor=target.vit_max,
            defensor_en_guardia=target.is_defending,
        )
        # ── RITMO: Corrupción / Petrificación ──
        if "Corrupción" in target.estados:
            danio = danio * 2
        if "Petrificación" in target.estados:
            danio = max(1, danio - 20)
        target.vit = max(0, target.vit - danio)
        target.is_defending = False

        lineas_resultado.append(f"🌀 **{fighter.name}** usa **{hab['nombre']}** → **{target.name}**: {texto}")

        # ── RITMO: Nivel 3 → técnica doble ──
        if tecnica_doble and target.alive:
            texto2, danio2, evadido2 = cmath.resolver_golpe_fisico(
                bono_dado=fue_ef,
                dano_base=dano_fisico,
                tipo_dano=tipo_dano,
                agi_efectiva_atacante=fighter.agi_efectiva,
                agi_efectiva_defensor=target.agi_efectiva,
                armadura_defensor=target.armadura_combinada,
                vit_max_defensor=target.vit_max,
                defensor_en_guardia=False,
            )
            if "Corrupción" in target.estados:
                danio2 = danio2 * 2
            if "Petrificación" in target.estados:
                danio2 = max(1, danio2 - 20)
            target.vit = max(0, target.vit - danio2)
            lineas_resultado.append(f"🌀 **{fighter.name}** repite **{hab['nombre']}** → **{target.name}**: {texto2}")

        result_line = "\n".join(lineas_resultado)

        # ── RITMO: Si permite acción extra, NO avanzar turno aún ──
        if permite_accion_extra:
            # Verificar si el combate terminó primero
            terminado, msg_oleada = session.is_truly_over()
            if msg_oleada:
                result_line += f"\n\n{msg_oleada}"
            if terminado:
                await _end_combat_victory(interaction, session, result_line)
                return

            # Publicar resultado parcial y mostrar botones de acción extra
            embed = session.status_embed()
            embed.description = result_line + "\n\n" + embed.description
            await interaction.response.send_message("Acción registrada.", ephemeral=True)
            await _publish(interaction, session, embed)

            # Enviar vista efímera con los botones
            view = AccionExtraView(session, fighter, target, hab)
            try:
                await interaction.followup.send(
                    "🔥 ¡Combo! Elegí tu acción extra (30s):",
                    view=view, ephemeral=True
                )
            except Exception:
                # Si falla el followup, avanzar turno normalmente
                npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
                texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")
                if combate_termino:
                    await _end_combat_victory(interaction, session, texto_completo)
                    return
                embed = session.status_embed()
                embed.description = texto_completo + "\n\n" + embed.description
                await _publish(interaction, session, embed)
            return

        # Flujo normal (sin acción extra)
        terminado, msg_oleada = session.is_truly_over()
        if msg_oleada:
            result_line += f"\n\n{msg_oleada}"
        if terminado:
            await _end_combat_victory(interaction, session, result_line)
            return

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /transformar ─────────────────────────────────────────────
    @bot.tree.command(name="transformar", description="Activa o desactiva una transformación")
    @app_commands.describe(personaje="Tu personaje", transformacion="Nombre de la transformación")
    @app_commands.autocomplete(personaje=personaje_autocomplete, transformacion=transformacion_autocomplete)
    async def transformar(interaction: discord.Interaction, personaje: str, transformacion: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return
        if session.paused:
            await interaction.response.send_message("El combate está pausado.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: verificar estado bloqueante ──
        bloqueo = fighter.tiene_estado_bloqueante("transformar")
        if bloqueo:
            await interaction.response.send_message(bloqueo, ephemeral=True)
            return

        # ── RITMO: transformar reinicia todos los contadores ──
        fighter.resetear_ritmo()

        trans_key = transformacion.lower()
        if fighter.transformado:
            if trans_key != fighter.transformacion_activa["name"].lower():
                await interaction.response.send_message(
                    f"Ya estás transformado como **{fighter.transformacion_activa['name']}**. Desactivá esa primero.",
                    ephemeral=True,
                )
                return
            fighter.desactivar_transformacion()
            result_line = f"🔄 **{fighter.name}** revierte su transformación."
        else:
            trans = fighter.transformaciones.get(trans_key)
            if not trans:
                await interaction.response.send_message("Transformación no encontrada.", ephemeral=True)
                return
            if fighter.mana < 2:
                await interaction.response.send_message("Necesitás al menos 2 MANA para transformarte.", ephemeral=True)
                return
            fighter.activar_transformacion(trans)
            result_line = f"⚡ **{fighter.name}** se transforma en **{trans['name']}**!"

        npc_texto, combate_termino = await _avanzar_y_resolver_npcs(session)
        texto_completo = result_line + (f"\n\n{npc_texto}" if npc_texto else "")

        if combate_termino:
            await _end_combat_victory(interaction, session, texto_completo)
            return

        embed = session.status_embed()
        embed.description = texto_completo + "\n\n" + embed.description
        await interaction.response.send_message("Acción registrada.", ephemeral=True)
        await _publish(interaction, session, embed)

    # ── /pausa ───────────────────────────────────────────────────
    @bot.tree.command(name="pausa", description="Pide pausar el combate (necesita consenso)")
    @app_commands.describe(personaje="Tu personaje (para verificar que estás en el combate)")
    @app_commands.autocomplete(personaje=personaje_autocomplete)
    async def pausa(interaction: discord.Interaction, personaje: str = None):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return

        if interaction.user.id not in session.owner_ids():
            await interaction.response.send_message("No participás en este combate.", ephemeral=True)
            return

        session.pause_votes.add(interaction.user.id)
        needed = session.owner_ids()

        if session.pause_votes >= needed:
            session.paused = True
            session.pause_votes.clear()
            embed = session.status_embed(title="⏸️ Combate pausado")
            await interaction.response.send_message("⏸️ Combate pausado por consenso.", ephemeral=True)
            await _publish(interaction, session, embed)
        else:
            await interaction.response.send_message(
                f"Voto para pausar registrado ({len(session.pause_votes)}/{len(needed)}).",
                ephemeral=True,
            )

    # ── /terminar ────────────────────────────────────────────────
    @bot.tree.command(name="terminar", description="Pide terminar el combate sin resultado (necesita consenso)")
    async def terminar(interaction: discord.Interaction):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return

        if interaction.user.id not in session.owner_ids():
            await interaction.response.send_message("No participás en este combate.", ephemeral=True)
            return

        session.terminate_votes.add(interaction.user.id)
        needed = session.owner_ids()

        if session.terminate_votes >= needed:
            embed = session.status_embed(title="🚪 Combate terminado por consenso")
            await interaction.response.send_message("🚪 Combate terminado.", ephemeral=True)
            await _publish(interaction, session, embed)
            _quitar_combate(session.channel_id, session)
        else:
            await interaction.response.send_message(
                f"Voto para terminar registrado ({len(session.terminate_votes)}/{len(needed)}).",
                ephemeral=True,
            )

    # ── /rendirse ────────────────────────────────────────────────
    @bot.tree.command(name="rendirse", description="Rinde todo tu equipo (no necesita consenso)")
    @app_commands.describe(personaje="Tu personaje")
    @app_commands.autocomplete(personaje=personaje_autocomplete)
    async def rendirse(interaction: discord.Interaction, personaje: str):
        session = _get_active_session(interaction)
        if not session:
            await interaction.response.send_message("No hay combate activo en este canal.", ephemeral=True)
            return

        fighter, err = _validate_turn(session, interaction, personaje)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return

        # ── RITMO: rendirse reinicia ritmo ──
        fighter.resetear_ritmo()

        equipo = fighter.team
        result_line = f"🏳️ **{fighter.name}** se rinde. Equipo {equipo + 1} pierde."
        winning_team = 1 - equipo
        await _end_combat_victory(interaction, session, result_line)
