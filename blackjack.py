#!/usr/bin/env python3
"""Блэкджек в терминале.

    python3 blackjack.py                  # умный дилер, 6 колод, банк 1000
    python3 blackjack.py --dealer s17     # дилер по правилам казино
    python3 blackjack.py --hints          # совет на каждом ходу
    python3 blackjack.py --hint-style odds  # вид совета: words, odds или ev
    python3 blackjack.py --classic        # прежний интерфейс без сукна
    python3 blackjack.py --help           # все настройки

Управление: H — ещё, S — хватит, D — удвоить, P — разделить, ? — совет,
T — вид совета, Q — выход. Ставка — стрелками ← → или цифрами, Enter — раздать.
Клавиши работают и в русской раскладке. Зависимостей нет, нужен Python 3.9+.
"""

from __future__ import annotations

import argparse
import os
import random
import select
import shutil
import signal
import sys
import textwrap
import time
import unicodedata
from functools import lru_cache
from typing import NamedTuple

try:
    import termios
    import tty
except ImportError:  # Windows
    termios = tty = None

# ─── Правила и настройки ─────────────────────────────────────────────────

MAX_HANDS = 4        # после сплитов — не больше четырёх рук
DEAL_DELAY = 0.25    # пауза между картами при раздаче, секунд
DEALER_DELAY = 0.7   # пауза между картами дилера

DEALERS = {
    "smart": ("умный", "видит ваши карты, знает, что осталось в шузе, и берёт карту, "
                       "только когда это ему выгодно. Правила «до 17» у него нет"),
    "s17": ("казино S17", "берёт карты до 17, на мягких 17 останавливается"),
    "h17": ("казино H17", "берёт карты до 17, на мягких 17 (например, туз + 6) берёт ещё"),
}

# ─── Карты ───────────────────────────────────────────────────────────────

SUITS = "♠♥♦♣"
RANKS = ("A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K")
RANK_VALUE = {rank: min(i + 1, 10) for i, rank in enumerate(RANKS)}


class Card(NamedTuple):
    rank: str
    suit: str

    @property
    def value(self) -> int:
        return RANK_VALUE[self.rank]

    @property
    def red(self) -> bool:
        return self.suit in "♥♦"


def best_total(hard: int, has_ace: bool) -> int:
    """Туз считается за 11, если это не приводит к перебору, иначе за 1."""
    return hard + 10 if has_ace and hard + 10 <= 21 else hard


class Hand:
    def __init__(self, cards=(), bet=0):
        self.cards: list[Card] = list(cards)
        self.bet = bet
        self.split = False    # рука из сплита: 21 из двух карт здесь не блэкджек
        self.outcome = None   # после расчёта: "blackjack", "win", "push", "lose"
        self.net = 0          # выигрыш (+) или проигрыш (−) по руке

    @property
    def hard(self) -> int:
        return sum(card.value for card in self.cards)

    @property
    def has_ace(self) -> bool:
        return any(card.rank == "A" for card in self.cards)

    @property
    def total(self) -> int:
        return best_total(self.hard, self.has_ace)

    @property
    def soft(self) -> bool:
        return self.total != self.hard

    @property
    def busted(self) -> bool:
        return self.total > 21

    @property
    def blackjack(self) -> bool:
        return not self.split and len(self.cards) == 2 and self.total == 21

    @property
    def pair(self) -> bool:
        return len(self.cards) == 2 and self.cards[0].value == self.cards[1].value


class Shoe:
    def __init__(self, decks: int):
        self.decks = decks
        self.shuffle()

    def shuffle(self):
        self.cards = [Card(r, s) for _ in range(self.decks) for s in SUITS for r in RANKS]
        random.shuffle(self.cards)

    def draw(self) -> Card:
        if not self.cards:  # шуз кончился посреди раздачи — берём новый
            self.shuffle()
        return self.cards.pop()

    def counts(self) -> tuple[int, ...]:
        """Сколько осталось карт каждого значения: туз, 2, …, 9, десятки."""
        counts = [0] * 10
        for card in self.cards:
            counts[card.value - 1] += 1
        return tuple(counts)

    @property
    def low(self) -> bool:
        """Осталось меньше четверти — пора перемешивать."""
        return len(self.cards) < max(15, self.decks * 13)


# ─── Дилер ───────────────────────────────────────────────────────────────

def dealer_hits(mode: str, dealer: Hand, hands: list[Hand], counts: tuple[int, ...]) -> bool:
    if mode == "s17":
        return dealer.total < 17
    if mode == "h17":
        return dealer.total < 17 or (dealer.total == 17 and dealer.soft)
    live = tuple((hand.total, hand.bet) for hand in hands if not hand.busted)
    return smart_dealer_hits(dealer.hard, dealer.has_ace, live, counts)


def smart_dealer_hits(hard: int, has_ace: bool, live, counts) -> bool:
    """Умный дилер перебирает все варианты добора из оставшегося шуза и берёт
    карту, только если в среднем это выгоднее, чем остановиться.

    live — пары (сумма, ставка) для рук игрока без перебора."""
    if not live:
        return False
    at_stake = sum(bet for _, bet in live)

    def options(hard, has_ace, counts):
        """Средний выигрыш дилера, если остановиться и если взять карту."""
        total = best_total(hard, has_ace)
        stand = sum(bet * ((total > t) - (total < t)) for t, bet in live)
        n = sum(counts)
        if stand == at_stake or total == 21 or n == 0:
            return stand, None
        hit = 0.0
        for i, k in enumerate(counts):
            if not k:
                continue
            if hard + i + 1 > 21:
                hit -= k * at_stake
            else:
                rest = counts[:i] + (k - 1,) + counts[i + 1:]
                hit += k * best(hard + i + 1, has_ace or i == 0, rest)
        return stand, hit / n

    @lru_cache(maxsize=None)
    def best(hard, has_ace, counts):
        stand, hit = options(hard, has_ace, counts)
        return stand if hit is None else max(stand, hit)

    stand, hit = options(hard, has_ace, counts)
    return hit is not None and hit > stand + 1e-9


# ─── Советчик ────────────────────────────────────────────────────────────

class Odds(NamedTuple):
    """Оценка хода: средний результат в долях ставки (+0.1 — это +10 %)
    и шансы выиграть, сыграть вничью и проиграть раздачу."""
    ev: float
    win: float
    push: float
    lose: float


WIN, PUSH, LOSE = Odds(1, 1, 0, 0), Odds(0, 0, 1, 0), Odds(-1, 0, 0, 1)


def mix(parts) -> Odds:
    """Среднее оценок с весами: parts — пары (вероятность, Odds)."""
    total = [0.0] * 4
    for q, odds in parts:
        for k in range(4):
            total[k] += q * odds[k]
    return Odds(*total)


def better(*options: Odds) -> Odds:
    return max(options, key=lambda odds: odds.ev)


def doubled(odds: Odds) -> Odds:
    """Две ставки на кону: средний результат вдвое больше, шансы те же."""
    return odds._replace(ev=2 * odds.ev)


def advise(hand: Hand, up: Card, mode: str, counts, actions) -> dict[str, Odds]:
    """Оценка каждого действия при лучшей дальнейшей игре.

    Считается для текущей руки так, будто она одна, по составу оставшегося
    шуза, но без учёта того, что карты уходят по ходу раздачи."""
    n = sum(counts)
    p = [k / n for k in counts]
    # Блэкджека у дилера нет — он уже проверил закрытую карту
    hole = [0.0 if (up.value == 1 and i == 9) or (up.value == 10 and i == 0) else q
            for i, q in enumerate(p)]
    hole = [q / sum(hole) for q in hole]

    @lru_cache(maxsize=None)
    def dealer_plays(hard, has_ace, t) -> Odds:
        """Исход для игрока с суммой t, пока дилер доигрывает свою руку."""
        total = best_total(hard, has_ace)
        now = WIN if t > total else PUSH if t == total else LOSE
        if mode == "smart":
            done = total == 21
        else:
            done = total > 17 or total == 17 and not (mode == "h17" and total != hard)
        if done:
            return now
        hit = mix((q, WIN if hard + i + 1 > 21 else dealer_plays(hard + i + 1, has_ace or i == 0, t))
                  for i, q in enumerate(p) if q)
        return min(now, hit, key=lambda odds: odds.ev) if mode == "smart" else hit

    @lru_cache(maxsize=None)
    def stand_at(t) -> Odds:
        return mix((q, dealer_plays(up.value + i + 1, up.value == 1 or i == 0, t))
                   for i, q in enumerate(hole) if q)

    def stand_on(hard, has_ace):
        return stand_at(best_total(hard, has_ace))

    def after_card(hard, has_ace, then):
        """Исход после ещё одной карты; перебор — проигрыш."""
        return mix((q, LOSE if hard + i + 1 > 21 else then(hard + i + 1, has_ace or i == 0))
                   for i, q in enumerate(p) if q)

    @lru_cache(maxsize=None)
    def play_on(hard, has_ace):
        """Лучший исход, если дальше можно и брать, и остановиться."""
        now = stand_on(hard, has_ace)
        if best_total(hard, has_ace) == 21:
            return now
        return better(now, after_card(hard, has_ace, play_on))

    def double_on(hard, has_ace):
        return doubled(after_card(hard, has_ace, stand_on))

    odds = {"h": after_card(hand.hard, hand.has_ace, play_on), "s": stand_on(hand.hard, hand.has_ace)}
    if "d" in actions:
        odds["d"] = double_on(hand.hard, hand.has_ace)
    if "p" in actions:
        value = hand.cards[0].value
        if value == 1:  # тузы после сплита получают по одной карте
            one = after_card(1, True, stand_on)
        else:
            one = after_card(value, False, lambda h, a: better(play_on(h, a), double_on(h, a)))
        odds["p"] = doubled(one)  # две руки — две ставки; шансы — для каждой руки
    return odds


# ─── Игра ────────────────────────────────────────────────────────────────

class Quit(Exception):
    """Игрок решил выйти."""


class Game:
    def __init__(self, ui, mode="smart", decks=6, bank=1000):
        self.ui = ui
        self.mode = mode
        self.shoe = Shoe(decks)
        self.start_bank = bank
        self.reset()

    def reset(self):
        self.bank = self.start_bank
        self.rounds = 0
        self.dealer = Hand()
        self.hands: list[Hand] = []
        self.active = None        # индекс руки, которой сейчас ходит игрок
        self.hole_hidden = False
        self.messages: list[str] = []
        self.history: list[str] = []  # итог каждой раздачи: blackjack, win, push или lose

    def deal(self, hand: Hand, delay=DEAL_DELAY):
        hand.cards.append(self.shoe.draw())
        self.ui.show(self, delay)

    def actions(self, hand: Hand) -> list[str]:
        actions = ["h", "s"]
        if len(hand.cards) == 2 and self.bank >= hand.bet:
            actions.append("d")
            if hand.pair and len(self.hands) < MAX_HANDS:
                actions.append("p")
        return actions

    def play_round(self, bet: int):
        self.rounds += 1
        self.messages = []
        if self.shoe.low:
            self.shoe.shuffle()
            self.messages.append("Шуз перемешан")
        self.bank -= bet
        self.hands = [Hand(bet=bet)]
        self.dealer = Hand()
        self.hole_hidden = True
        for _ in range(2):
            self.deal(self.hands[0])
            self.deal(self.dealer)

        # Блэкджек у дилера возможен только с тузом или десяткой в открытую,
        # и тогда он сразу проверяет закрытую карту — раздача заканчивается.
        if not self.dealer.blackjack and not self.hands[0].blackjack:
            self.player_turn()
            self.dealer_turn()
        self.settle()

    def player_turn(self):
        i = 0
        while i < len(self.hands):
            self.active = i
            hand = self.hands[i]
            if len(hand.cards) == 1:  # вторая карта руке после сплита
                self.ui.show(self, DEAL_DELAY * 2)
                self.deal(hand, 0)
            while hand.total < 21 and not (hand.split and hand.cards[0].rank == "A"):
                action = self.ui.choose(self, hand, self.actions(hand))
                if action == "s":
                    break
                if action == "h":
                    self.deal(hand, 0)
                elif action == "d":
                    self.bank -= hand.bet
                    hand.bet *= 2
                    self.deal(hand)
                    break
                elif action == "p":
                    self.bank -= hand.bet
                    new = Hand([hand.cards.pop()], hand.bet)
                    hand.split = new.split = True
                    self.hands.insert(i + 1, new)
                    self.ui.show(self, DEAL_DELAY * 2)  # видно, что в руке осталась одна карта
                    self.deal(hand, 0)
            i += 1
        self.active = None

    def dealer_turn(self):
        self.hole_hidden = False
        self.ui.show(self, DEALER_DELAY)
        if all(hand.busted for hand in self.hands):
            return
        while dealer_hits(self.mode, self.dealer, self.hands, self.shoe.counts()):
            self.deal(self.dealer, DEALER_DELAY)
        if self.dealer.busted:
            self.messages.append("У дилера перебор")
        else:
            self.messages.append(f"Дилер остановился на {self.dealer.total}")

    def settle(self):
        self.active = None
        self.hole_hidden = False
        dealer = self.dealer
        if dealer.blackjack:
            self.messages.append("У дилера блэкджек")
        for hand in self.hands:
            if hand.blackjack and not dealer.blackjack:
                hand.outcome, hand.net = "blackjack", hand.bet * 1.5
            elif hand.busted:
                hand.outcome, hand.net = "lose", -hand.bet
            elif dealer.busted or hand.total > dealer.total:
                hand.outcome, hand.net = "win", hand.bet
            elif hand.total == dealer.total:
                hand.outcome, hand.net = "push", 0
            else:
                hand.outcome, hand.net = "lose", -hand.bet
            self.bank += hand.bet + hand.net
        net = sum(h.net for h in self.hands)
        if len(self.hands) > 1:
            self.messages.append("Итог раздачи: " + signed(net))
        self.history.append("blackjack" if any(h.outcome == "blackjack" for h in self.hands)
                            else "win" if net > 0 else "lose" if net < 0 else "push")


# ─── Отрисовка ───────────────────────────────────────────────────────────

COLOR = sys.stdout.isatty() and "NO_COLOR" not in os.environ
BOLD, DIM, RED, GREEN, YELLOW, BLUE, CYAN = "1", "2", "31", "32", "33", "34", "36"
ORANGE = "38;5;215"

ACTIONS = {"h": "ещё", "s": "хватит", "d": "удвоить", "p": "разделить"}
OUTCOMES = {
    "blackjack": ("блэкджек", YELLOW),
    "win": ("победа", GREEN),
    "push": ("ничья", YELLOW),
    "lose": ("проигрыш", RED),
}

# Виды совета: название и что показывает оценка под клавишей
HINT_STYLES = {
    "words": ("словами", "«лучший», «тоже ок», «хуже» или «ошибка»"),
    "odds": ("шансы", "вероятность выиграть раздачу, если сыграть так"),
    "ev": ("матожидание", "сколько фишек ход приносит в среднем"),
}


def paint(text, *styles) -> str:
    if not COLOR or not styles:
        return str(text)
    return f"\033[{';'.join(styles)}m{text}\033[0m"


def money(x) -> str:
    text = f"{int(x):,}" if x == int(x) else f"{x:,.1f}"
    return text.replace(",", " ")


def signed(x) -> str:
    return ("+" if x > 0 else "−" if x < 0 else "") + money(abs(x))


# Оттенок оценки хода → стиль в классическом интерфейсе (на сукне — свои цвета)
CLASSIC_TONES = {"best": (BOLD, YELLOW), "good": (GREEN,), "meh": (ORANGE,), "bad": (RED,),
                 "plus": (GREEN,), "minus": (RED,), "plain": (), "zero": (DIM,)}


def amount(x) -> tuple[str, str]:
    """Средний выигрыш в фишках: +3.0, −2.1 или 0 — и его оттенок."""
    digits = 2 if abs(x) < 1 else 1 if abs(x) < 10 else 0
    if not round(x, digits):
        return "0", "zero"
    return f"{x:+.{digits}f}".replace("-", "−"), "plus" if x > 0 else "minus"


def rate(odds: dict[str, Odds], action: str, style: str, bet) -> tuple[str, str]:
    """Оценка хода в выбранном виде совета: текст и оттенок."""
    best = max(odds, key=lambda a: odds[a].ev)
    if style == "odds":
        return f"{odds[action].win * 100:.0f}%", "best" if action == best else "plain"
    if style == "ev":
        return amount(odds[action].ev * bet)
    gap = odds[best].ev - odds[action].ev  # в долях ставки
    if action == best:
        return "лучший", "best"
    if gap < 0.02:
        return "тоже ок", "good"
    if gap < 0.15:
        return "хуже", "meh"
    return "ошибка", "bad"


def hint_ratings(game: Game, hand: Hand, actions, style: str) -> tuple[str, dict[str, tuple[str, str]]]:
    """Лучший ход и оценка каждого доступного хода."""
    odds = advise(hand, game.dealer.cards[0], game.mode, game.shoe.counts(), actions)
    best = max(odds, key=lambda a: odds[a].ev)
    return best, {a: rate(odds, a, style, hand.bet) for a in odds}


def key_label(key: str) -> str:
    return paint(f"[{key}]", BOLD, CYAN)


def card_style(card: Card) -> tuple[str, ...]:
    return (BOLD, RED) if card.red else (BOLD,)


def card_art(card: Card | None) -> list[str]:
    """Карта 9×5 символов; None — рубашка."""
    if card is None:
        rows = [paint("░" * 7, BLUE)] * 3
    else:
        label = card.rank + card.suit
        rows = [paint(f"{label:<7}", *card_style(card)),
                paint(f"{card.suit:^7}", *card_style(card)),
                paint(f"{label:>7}", *card_style(card))]
    return ["╭───────╮", *(f"│{row}│" for row in rows), "╰───────╯"]


def card_short(card: Card | None) -> str:
    if card is None:
        return paint("[??]", BLUE)
    return paint(f"[{card.rank}{card.suit}]", *card_style(card))


def cards_block(cards, hide_hole: bool, compact: bool, width: int) -> list[str]:
    shown = [None if hide_hole and i == 1 else card for i, card in enumerate(cards)]
    if compact:
        return ["  " + " ".join(card_short(card) for card in shown)]
    if not shown:  # место под карты, чтобы стол не прыгал во время раздачи
        return [""] * 5
    per_row = max(1, (width - 2) // 10)
    lines = []
    for start in range(0, len(shown), per_row):
        arts = [card_art(card) for card in shown[start:start + per_row]]
        lines += ["  " + " ".join(row) for row in zip(*arts)]
    return lines


def total_text(hand: Hand, hide_hole=False) -> str:
    if not hand.cards:
        return ""
    if hide_hole:
        up = hand.cards[0]
        return paint(f"{'A' if up.rank == 'A' else up.value} + ?", BOLD)
    if hand.blackjack:
        return paint("БЛЭКДЖЕК", BOLD, YELLOW)
    if hand.busted:
        return paint(f"{hand.total} перебор", BOLD, RED)
    if hand.soft and hand.total < 21:
        return paint(f"{hand.hard} / {hand.total}", BOLD)
    return paint(hand.total, BOLD)


def intro_items(game: Game, width: int) -> list[tuple[str, str]]:
    """Правила и виды совета для стартового экрана: (текст, вид) — text или title."""
    name, about = DEALERS[game.mode]
    rules = [
        "блэкджек платит 3:2, при ничьей ставка возвращается",
        "если у дилера открыт туз или десятка, он сразу проверяет, нет ли у него блэкджека",
        "удвоить можно на любых двух картах, в том числе после сплита",
        f"пару можно разделить, всего до {MAX_HANDS} рук; тузы после сплита получают по одной карте",
        f"дилер {name}: {about}",
    ]
    items = [("Правила", "title")]
    for rule in rules:
        items += [(line, "text") for line in textwrap.wrap(rule, width, initial_indent="• ", subsequent_indent="  ")]
    items += [("", "text"), ("Совет (?) — лучший ход и оценка остальных. Вид меняется клавишей T:", "title")]
    items += [(f"• {style} — {about}", "text") for style, about in HINT_STYLES.values()]
    return items


def intro_lines(game: Game, width: int) -> list[str]:
    lines = ["", "  Сделайте ставку, чтобы начать.", ""]
    lines += [f"  {paint(text, BOLD) if kind == 'title' else text}" if text else ""
              for text, kind in intro_items(game, width - 4)]
    lines += ["", paint("  H — ещё, S — хватит, D — удвоить, P — разделить, ? — совет, Q — выход", DIM)]
    return lines


def table_lines(game: Game, compact: int, width: int) -> list[str]:
    """compact: 0 — все карты большие, 1 — руки игрока в строку, 2 — всё в строку."""
    lines = [f"  {paint('🃏 БЛЭКДЖЕК', BOLD)}   Банк: {paint(money(game.bank), BOLD, GREEN)}   "
             + paint(f"дилер: {DEALERS[game.mode][0]} · колод: {game.shoe.decks}", DIM)]
    if not game.hands:
        return lines + intro_lines(game, width)

    dealer = game.dealer
    lines += ["", f"  {paint('ДИЛЕР', BOLD)}  {total_text(dealer, game.hole_hidden)}"]
    lines += cards_block(dealer.cards, game.hole_hidden, compact >= 2, width)

    many = len(game.hands) > 1
    for i, hand in enumerate(game.hands):
        name = f"РУКА {i + 1}" if many else "ВЫ"
        marker = paint("▶ ", BOLD, YELLOW) if many and i == game.active else "  "
        label = f"{marker}{paint(name, BOLD)}  {total_text(hand)}   " + paint(f"ставка {money(hand.bet)}", DIM)
        if hand.outcome:
            text, color = OUTCOMES[hand.outcome]
            label += "   " + paint(f"{text} {signed(hand.net)}" if hand.net else text, BOLD, color)
        lines += ["", label] + cards_block(hand.cards, False, compact >= 1, width)

    if game.messages:
        lines.append("")
        lines += [f"  {paint('•', DIM)} {message}" for message in game.messages[-2:]]
    return lines


def controls(actions, ratings=None) -> list[str]:
    """Строка клавиш; если есть оценки ходов — вторая строка, каждая оценка под своей клавишей."""
    items = [(f"[{a.upper()}]", name, ratings.get(a) if ratings else None)
             for a, name in ACTIONS.items() if a in actions]
    items += [("[T]" if ratings else "[?]", "вид" if ratings else "совет", None), ("[Q]", "выход", None)]
    line, under, x, end = "  ", "", 2, 0
    for key, name, rated in items:
        line += f"{key_label(key[1:-1])} {name}   "
        width = len(key) + 1 + len(name)
        if rated:
            start = max(end + 1, x + (width - len(rated[0])) // 2)
            under += " " * (start - end) + paint(rated[0], *CLASSIC_TONES[rated[1]])
            end = start + len(rated[0])
        x += width + 3
    return [line.rstrip()] + ([under] if ratings else [])


# ─── Ввод ────────────────────────────────────────────────────────────────

# Те же физические клавиши в русской раскладке
KEYMAP = {
    "h": "h", "р": "h",
    "s": "s", "ы": "s",
    "d": "d", "в": "d",
    "p": "p", "з": "p",
    "q": "q", "й": "q",
    "y": "y", "н": "y",
    "n": "n", "т": "n",
    "t": "t", "е": "t",
    "?": "?", "/": "?", ",": "?", ".": "?",
    "\n": "enter", "\r": "enter", " ": "enter",
}
ARROWS = {b"A": "up", b"B": "down", b"C": "right", b"D": "left"}  # ESC [ A или ESC O A


class Keyboard:
    """Нажатия без Enter: на время игры терминал переводится в режим cbreak.
    Если ввод не терминал (например, pipe), читаем построчно."""

    def __init__(self):
        self.fd = sys.stdin.fileno() if termios and sys.stdin.isatty() else None
        self.saved = None
        self.resized = False  # окно изменило размер — key() вернёт "resize", чтобы перерисовать

    def __enter__(self):
        if self.fd is not None:
            self.saved = termios.tcgetattr(self.fd)
            tty.setcbreak(self.fd)
        return self

    def __exit__(self, *exc):
        if self.saved is not None:
            termios.tcsetattr(self.fd, termios.TCSADRAIN, self.saved)

    def key(self) -> str:
        """Одна клавиша: символ или up, down, left, right, backspace, resize."""
        if self.fd is not None:
            termios.tcflush(self.fd, termios.TCIFLUSH)  # нажатия во время анимации не в счёт
            while not select.select([self.fd], [], [], 0.2)[0]:
                if self.resized:
                    self.resized = False
                    return "resize"
            data = os.read(self.fd, 16)
            if data.startswith(b"\x1b"):
                return ARROWS.get(data[-1:], "") if len(data) == 3 else ""
            if data in (b"\x7f", b"\x08"):
                return "backspace"
            return data.decode("utf-8", "ignore")[:1]
        if os.name == "nt" and sys.stdin.isatty():
            import msvcrt
            key = msvcrt.getwch()
            if key in ("\x00", "\xe0"):  # стрелки в консоли Windows
                return {"H": "up", "P": "down", "K": "left", "M": "right"}.get(msvcrt.getwch(), "")
            return "backspace" if key == "\x08" else key
        line = sys.stdin.readline()
        if not line:
            raise Quit
        return line.strip()[:1] or "\n"

    def line(self, prompt: str) -> str:
        try:
            if self.fd is None:
                return input(prompt)
            termios.tcflush(self.fd, termios.TCIFLUSH)
            termios.tcsetattr(self.fd, termios.TCSADRAIN, self.saved)
            try:
                return input(prompt)
            finally:
                tty.setcbreak(self.fd)
        except EOFError:
            raise Quit from None


# ─── Интерфейс ───────────────────────────────────────────────────────────

class TerminalUI:
    def __init__(self, keyboard: Keyboard, hints=False, hint_style="words"):
        self.kb = keyboard
        self.hints = hints
        self.hint_style = hint_style
        self.last_bet = 50
        self.screen = sys.stdout.isatty()

    def show(self, game: Game, delay=0.0, footer=()):
        width, height = shutil.get_terminal_size()
        for compact in range(3):
            lines = table_lines(game, compact, width)
            if len(lines) + len(footer) + 2 <= height:
                break
        lines += [""] + list(footer)
        if self.screen:
            sys.stdout.write("\033[H" + "".join(line + "\033[K\n" for line in lines) + "\033[J")
            sys.stdout.flush()
            if delay:
                time.sleep(delay)
        else:
            print("\n".join(lines))

    def choose(self, game: Game, hand: Hand, actions) -> str:
        hint = self.hints
        while True:
            self.show(game, footer=self.hint_footer(game, hand, actions) if hint else controls(actions))
            key = KEYMAP.get(self.kb.key().lower())
            if key in actions:
                return key
            if key == "?":
                hint = True
            elif key == "t":  # следующий вид совета — и сразу показать его
                self.next_hint_style()
                hint = True
            elif key == "q" and self.confirm(game, "Выйти из игры? Ставка на столе сгорит."):
                raise Quit

    def next_hint_style(self):
        styles = list(HINT_STYLES)
        self.hint_style = styles[(styles.index(self.hint_style) + 1) % len(styles)]

    def hint_footer(self, game: Game, hand: Hand, actions) -> list[str]:
        """Лучший ход, а под каждой клавишей — оценка хода в выбранном виде."""
        best, ratings = hint_ratings(game, hand, actions, self.hint_style)
        return ([f"  💡 Совет: {paint(ACTIONS[best].upper(), BOLD, YELLOW)}   "
                 + paint(f"вид: {HINT_STYLES[self.hint_style][0]}", DIM)]
                + controls(actions, ratings))

    def confirm(self, game: Game, question: str) -> bool:
        self.show(game, footer=[f"  {question}   {key_label('Y')} да   {key_label('N')} нет"])
        while True:
            key = KEYMAP.get(self.kb.key().lower())
            if key in ("y", "n"):
                return key == "y"

    def ask_bet(self, game: Game) -> int:
        error = None
        while True:
            default = min(self.last_bet, int(game.bank))
            footer = [paint(f"  За сессию: {signed(game.bank - game.start_bank)} · раздач: {game.rounds}", DIM)]
            if error:
                footer.append(paint(f"  {error}", RED))
            self.show(game, footer=footer)
            if self.screen:
                sys.stdout.write("\033[?25h")  # курсор нужен только при вводе ставки
            raw = self.kb.line(f"  Ставка (Enter — {money(default)}, Q — выход): ").strip().lower()
            if self.screen:
                sys.stdout.write("\033[?25l")
            if raw in ("q", "й"):
                raise Quit
            if not raw:
                bet = default
            elif raw.isdigit():
                bet = int(raw)
            else:
                error = "Введите число"
                continue
            if not 1 <= bet <= game.bank:
                error = f"Ставка должна быть от 1 до {money(int(game.bank))}"
                continue
            self.last_bet = bet
            return bet

    def game_over(self, game: Game) -> bool:
        self.show(game, footer=[paint("  💸 Банк пуст!", BOLD, RED),
                                f"  {key_label('Enter')} начать заново   {key_label('Q')} выход"])
        while True:
            key = KEYMAP.get(self.kb.key().lower())
            if key in ("enter", "q"):
                return key == "enter"


# ─── Сукно: интерфейс по умолчанию ───────────────────────────────────────

# 256-цветная палитра
FELT, BAR = 22, 235
CREAM, GOLD, FADED, FAINT, MUTED = 230, 220, 107, 65, 245
PAPER, EDGE, INK, SUIT_RED = 231, 250, 16, 160
BACK, PATTERN = 25, 32
CHIP_COLORS = [(500, 129), (100, 244), (25, 40), (5, 196), (1, 255)]
BADGES = {"plain": (236, PAPER), "active": (GOLD, INK), "bust": (124, PAPER), "blackjack": (GOLD, INK),
          "win": (28, PAPER), "lose": (88, PAPER), "push": (240, PAPER)}
KEYCAPS = {"on": (250, INK, 252), "best": (GOLD, INK, GOLD), "off": (237, 242, 240)}
TONES = {"best": GOLD, "good": 150, "meh": 215, "bad": 210,
         "plus": 114, "minus": 210, "plain": 252, "zero": MUTED}
HISTORY_MARKS = {"blackjack": ("★", GOLD), "win": ("●", 40), "push": ("●", 178), "lose": ("●", 196)}
TABLE_NOTES = {
    "smart": "дилер умный · видит ваши карты",
    "s17": "дилер берёт до 17 · на мягких 17 стоит",
    "h17": "дилер берёт до 17 · на мягких 17 берёт",
}
BET_STEPS = (1, 2, 5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10_000, 25_000, 50_000, 100_000)
TABLE_W, TABLE_H = 80, 24   # стол по центру окна; окно меньше — просим растянуть
BIG_CARDS_H = 32            # с такой высоты окна карты крупные
SLIDE_FRAMES, FRAME_TIME = 8, 0.016  # карта летит из шуза примерно 0.15 с


def text_width(text: str) -> int:
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in text)


class Canvas:
    """Экран как сетка клеток (символ, цвет, фон, жирный): рисуем слоями,
    выводим одной строкой — без мерцания."""

    def __init__(self, w: int, h: int, bg: int):
        self.w, self.h = w, h
        self.cells = [[[" ", PAPER, bg, False] for _ in range(w)] for _ in range(h)]

    def put(self, x, y, text, fg=None, bg=None, bold=False) -> int:
        """Пишет текст и возвращает x после него; fg/bg=None — оставить цвет клетки."""
        for ch in text:
            wide = unicodedata.east_asian_width(ch) in "WF"
            if 0 <= y < self.h and 0 <= x and x + wide < self.w:
                cell = self.cells[y][x]
                cell[:] = [ch, cell[1] if fg is None else fg, cell[2] if bg is None else bg, bold]
                if wide:  # вторая половина широкого символа
                    self.cells[y][x + 1][:] = ["", cell[1], cell[2], bold]
            x += 1 + wide
        return x

    def fill(self, x, y, w, h, bg):
        for row in range(y, y + h):
            self.put(x, row, " " * w, bg=bg)

    def center(self, cx, y, text, **style) -> int:
        return self.put(cx - text_width(text) // 2, y, text, **style)

    def render(self) -> str:
        rows = []
        for row in self.cells:
            out, last = [], None
            for ch, fg, bg, bold in row:
                if not ch:
                    continue
                if (fg, bg, bold) != last:
                    out.append(f"\033[{1 if bold else 22};38;5;{fg};48;5;{bg}m")
                    last = (fg, bg, bold)
                out.append(ch)
            rows.append("".join(out) + "\033[0m")
        return "\033[H" + "\n".join(rows)


def draw_segments(cv: Canvas, y: int, segments):
    """Строка из кусков (текст, цвет, фон, жирный) по центру экрана."""
    x = (cv.w - sum(text_width(text) for text, *_ in segments)) // 2
    for text, fg, bg, bold in segments:
        x = cv.put(x, y, text, fg=fg, bg=bg, bold=bold)


def cap(key: str, label: str, state="on"):
    """Кнопка-клавиша: куски для draw_segments."""
    cap_bg, cap_fg, label_fg = KEYCAPS[state]
    return [(f" {key} ", cap_fg, cap_bg, True), (f" {label}", label_fg, None, state == "best")]


def keycap_bar(cv: Canvas, items):
    """Нижняя панель кнопок. items — (клавиша, подпись, состояние, оценка);
    состояние: on, best (лучший ход) или off (недоступно); оценка пишется под кнопкой."""
    y = cv.h - 2
    cv.fill(0, y, cv.w, 2, BAR)
    widths = [text_width(key) + 3 + text_width(label) for key, label, _, _ in items]
    x = (cv.w - sum(widths) - 4 * (len(items) - 1)) // 2
    for (key, label, state, rated), width in zip(items, widths):
        cap_bg, cap_fg, label_fg = KEYCAPS[state]
        end = cv.put(x, y, f" {key} ", fg=cap_fg, bg=cap_bg, bold=True)
        cv.put(end + 1, y, label, fg=label_fg, bold=state == "best")
        if rated:
            text, tone = rated
            cv.put(x + (width - text_width(text)) // 2, y + 1, text, fg=TONES[tone], bold=tone == "best")
        x += width + 4


def text_bar(cv: Canvas, segments):
    cv.fill(0, cv.h - 2, cv.w, 2, BAR)
    draw_segments(cv, cv.h - 2, segments)


def card_frame(cv: Canvas, x, y, width, height):
    """Белая карта со скруглёнными углами из полублоков. Левая кромка серая —
    так видна граница, когда карты лежат веером."""
    cv.put(x, y, "▗", fg=EDGE)
    cv.put(x + 1, y, "▄" * (width - 2), fg=PAPER)
    cv.put(x + width - 1, y, "▖", fg=PAPER)
    for row in range(y + 1, y + height - 1):
        cv.put(x, row, " ", bg=EDGE)
        cv.put(x + 1, row, " " * (width - 1), bg=PAPER)
    cv.put(x, y + height - 1, "▝", fg=EDGE)
    cv.put(x + 1, y + height - 1, "▀" * (width - 2), fg=PAPER)
    cv.put(x + width - 1, y + height - 1, "▘", fg=PAPER)


# Раскладка мастей на крупной карте: (колонка, ряд) внутри карты 11×9
L_, M_, R_ = 3, 5, 7
PIPS = {
    1: [(M_, 2)],
    2: [(M_, 0), (M_, 4)],
    3: [(M_, 0), (M_, 2), (M_, 4)],
    4: [(L_, 0), (R_, 0), (L_, 4), (R_, 4)],
    5: [(L_, 0), (R_, 0), (M_, 2), (L_, 4), (R_, 4)],
    6: [(L_, 0), (R_, 0), (L_, 2), (R_, 2), (L_, 4), (R_, 4)],
    7: [(L_, 0), (R_, 0), (M_, 1), (L_, 2), (R_, 2), (L_, 4), (R_, 4)],
    8: [(L_, 0), (R_, 0), (M_, 1), (L_, 2), (R_, 2), (M_, 3), (L_, 4), (R_, 4)],
    9: [(L_, 0), (R_, 0), (L_, 1), (R_, 1), (M_, 2), (L_, 3), (R_, 3), (L_, 4), (R_, 4)],
    10: [(L_, 0), (R_, 0), (L_, 1), (M_, 1), (R_, 1), (L_, 3), (M_, 3), (R_, 3), (L_, 4), (R_, 4)],
}
FACES = {"J": "♞", "Q": "♛", "K": "♚"}


def draw_card(cv: Canvas, x, y, card: Card | None, big=False, width=None):
    """Карта 9×5 или крупная 11×9 с раскладкой мастей; None — рубашка.
    Ширина меньше обычной — кадр переворота: видно только угол, 1 — ребро."""
    full, height = (11, 9) if big else (9, 5)
    width = width or full
    if width == 1:
        cv.put(x, y, "▗", fg=EDGE)
        for row in range(y + 1, y + height - 1):
            cv.put(x, row, "▐", fg=EDGE)
        cv.put(x, y + height - 1, "▝", fg=EDGE)
        return
    card_frame(cv, x, y, width, height)
    if card is None:
        for k, row in enumerate(range(y + 1, y + height - 1)):
            cv.put(x + 1, row, (("▚▞" if k % 2 == 0 else "▞▚") * width)[:width - 2], fg=PATTERN, bg=BACK)
        return
    ink = SUIT_RED if card.red else INK
    label = card.rank + card.suit
    cv.put(x + 1, y + 1, label, fg=ink, bold=True)
    if width < full:
        return
    cv.put(x + width - 1 - len(label), y + height - 2, label, fg=ink, bold=True)
    if not big:
        cv.put(x + width // 2, y + 2, card.suit, fg=ink)
    elif card.rank in FACES:
        cv.put(x + 3, y + 2, "╭───╮", fg=ink)
        for row in range(y + 3, y + 6):
            cv.put(x + 3, row, "│   │", fg=ink)
        cv.put(x + 3, y + 6, "╰───╯", fg=ink)
        cv.put(x + 5, y + 3, card.suit, fg=ink)
        cv.put(x + 5, y + 4, FACES[card.rank], fg=ink, bold=True)
        cv.put(x + 5, y + 5, card.suit, fg=ink)
    else:
        for col, row in PIPS[1 if card.rank == "A" else int(card.rank)]:
            cv.put(x + col, y + 2 + row, card.suit, fg=ink)


def slots(n: int, cx: int, card_w: int, max_width: int) -> list[int]:
    """x каждой карты руки: с зазором, а если не помещаются — веером."""
    step = card_w + 1
    if n > 1 and n * step - 1 > max_width:
        step = max(3, (max_width - card_w) // (n - 1))
    left = cx - (card_w + (n - 1) * step) // 2
    return [left + i * step for i in range(n)]


def hand_badge(cards, split=False, hidden=False, outcome=None, active=False):
    """Сумма очков для подписи над картами: (текст, вид плашки) или None."""
    if not cards:
        return None
    if hidden:
        up = cards[0]
        return f"{'A' if up.rank == 'A' else up.value} + ?", "plain"
    hand = Hand(cards)
    hand.split = split
    if hand.blackjack:
        return "БЛЭКДЖЕК", "blackjack"
    text = f"{hand.total} перебор" if hand.busted else f"{hand.hard} / {hand.total}" \
        if hand.soft and hand.total < 21 else str(hand.total)
    kind = outcome or ("bust" if hand.busted else "active" if active else "plain")
    return text, kind


def chip_colors(amount, limit=5) -> list[int]:
    colors = []
    for value, color in CHIP_COLORS:
        while amount >= value and len(colors) < limit:
            colors.append(color)
            amount -= value
    return colors


class Layout:
    """Где что лежит: стол шириной 80 колонок по центру окна, по высоте — тоже."""

    def __init__(self, w: int, h: int):
        self.w, self.h = w, h
        self.big = h >= BIG_CARDS_H
        self.card_w, self.card_h = (11, 9) if self.big else (9, 5)
        self.ox = (w - TABLE_W) // 2
        self.cx = self.ox + TABLE_W // 2
        dy = max(0, (h - TABLE_H - 2 * (self.card_h - 5)) // 2)
        self.dealer = 2 + dy                        # подпись дилера, под ней карты
        self.table = self.dealer + self.card_h + 2  # надпись на сукне или баннер итога
        self.player = self.table + 3                # подпись руки, под ней карты
        self.marker = self.player + self.card_h + 1  # ▲ под рукой, которой ходите
        self.message = self.marker + 1              # сообщения, ниже — пояснение совета
        self.shoe_x = self.ox + 66


class FeltUI:
    """Интерфейс по умолчанию: зелёное сукно, белые карты, кнопки-клавиши, анимации.

    Игра вызывает те же методы, что и у TerminalUI. Новые карты и переворот
    закрытой карты интерфейс замечает сам, сравнивая стол с прошлым кадром."""

    DEALER_WIDTH = 50  # правее лежит шуз

    def __init__(self, keyboard: Keyboard, hints=False, hint_style="words"):
        self.kb = keyboard
        self.hints = hints
        self.hint_style = hint_style
        self.last_bet = 50
        self.seen_round = None           # раздача, для которой запомнены карты на столе
        self.seen: dict[int, int] = {}   # id руки → сколько её карт уже на столе
        self.hole_revealed = False
        self.buttons = None              # кнопки хода: не пропадают, пока летит карта
        if hasattr(signal, "SIGWINCH"):  # перерисуем, когда игра будет ждать клавишу
            signal.signal(signal.SIGWINCH, lambda *_: setattr(self.kb, "resized", True))

    next_hint_style = TerminalUI.next_hint_style

    # ── кадр ──

    def render(self, game: Game, bar, legend=None, banner=None):
        """Кадр целиком: стол, пояснение совета, нижняя панель bar(cv)."""
        w, h = shutil.get_terminal_size()
        if w < TABLE_W or h < TABLE_H:
            sys.stdout.write(f"\033[H\033[2J\033[0m  Окно маловато для стола: нужно хотя бы {TABLE_W}×{TABLE_H}, "
                             f"сейчас {w}×{h}.\n  Растяните окно или запустите blackjack --classic.")
            sys.stdout.flush()
            return
        layout = Layout(w, h)
        self.animate(game, layout, bar)
        cv = self.table(game, layout, banner=banner)
        if legend:
            cv.center(layout.cx, layout.message + 1, legend, fg=FADED)
        bar(cv)
        self.flush(cv)

    @staticmethod
    def flush(cv: Canvas):
        sys.stdout.write(cv.render())
        sys.stdout.flush()

    def table(self, game: Game, L: Layout, skip=None, flip=None, banner=None) -> Canvas:
        """Стол без нижней панели. skip — (рука, номер карты), которая ещё летит из шуза;
        flip — кадр переворота закрытой карты дилера: (ширина, лицом вверх)."""
        cv = Canvas(L.w, L.h, FELT)
        self.header(cv, game)
        if not game.hands:
            self.intro(cv, game, L)
            return cv
        self.shoe(cv, L, len(game.shoe.cards))
        banner = banner or self.result(game)
        if banner:
            self.banner(cv, L, *banner)
        else:
            cv.center(L.cx, L.table, "БЛЭКДЖЕК  ПЛАТИТ  3  К  2", fg=FADED, bold=True)
            cv.center(L.cx, L.table + 1, TABLE_NOTES[game.mode], fg=FAINT)

        dealer = game.dealer
        cards = self.visible(dealer, skip)
        hidden = game.hole_hidden or (flip is not None and not flip[1])
        self.label(cv, L.cx, L.dealer, "ДИЛЕР", hand_badge(cards, hidden=hidden), self.DEALER_WIDTH)
        for i, (card, x) in enumerate(zip(cards, slots(len(dealer.cards), L.cx, L.card_w, self.DEALER_WIDTH))):
            if i == 1 and flip:
                width, face_up = flip
                draw_card(cv, x + (L.card_w - width) // 2, L.dealer + 1, card if face_up else None, L.big, width)
            else:
                draw_card(cv, x, L.dealer + 1, None if i == 1 and game.hole_hidden else card, L.big)

        many = len(game.hands) > 1
        for i, (hand, cx, width) in enumerate(self.seats(game, L)):
            cards = self.visible(hand, skip)
            active = many and i == game.active
            name = (("РУКА " if width >= 22 else "") + str(i + 1)) if many else "ВЫ"
            badge = hand_badge(cards, hand.split, outcome=hand.outcome, active=active)
            self.label(cv, cx, L.player, name, badge, width, hand.bet, active)
            for card, x in zip(cards, slots(len(hand.cards), cx, L.card_w, width)):
                draw_card(cv, x, L.player + 1, card, L.big)
            if active:
                cv.center(cx, L.marker, "▲", fg=GOLD, bold=True)
        if game.messages:
            cv.center(L.cx, L.message, " · ".join(game.messages[-2:]), fg=CREAM)
        return cv

    @staticmethod
    def visible(hand: Hand, skip):
        return hand.cards[:skip[1]] if skip and skip[0] is hand else hand.cards

    @staticmethod
    def seats(game: Game, L: Layout):
        """Руки игрока стоят рядом: (рука, центр места, ширина места)."""
        region = (TABLE_W - 4) // len(game.hands)
        return [(hand, L.ox + 2 + region * i + region // 2, region - 2) for i, hand in enumerate(game.hands)]

    def card_xy(self, game: Game, L: Layout, hand: Hand, index: int):
        if hand is game.dealer:
            return slots(len(hand.cards), L.cx, L.card_w, self.DEALER_WIDTH)[index], L.dealer + 1
        for seat, cx, width in self.seats(game, L):
            if seat is hand:
                return slots(len(hand.cards), cx, L.card_w, width)[index], L.player + 1

    @staticmethod
    def header(cv: Canvas, game: Game):
        cv.fill(0, 0, cv.w, 1, BAR)
        x = cv.put(1, 0, "🃏 БЛЭКДЖЕК", fg=GOLD, bold=True)
        cv.put(x + 3, 0, f"дилер: {DEALERS[game.mode][0]}", fg=MUTED)
        marks = game.history[-8:]
        x = cv.w - 2 - len("банк ") - len(money(game.bank)) - (3 + 2 * len(marks) if marks else 0)
        x = cv.put(x, 0, "банк ", fg=MUTED)
        x = cv.put(x, 0, money(game.bank), fg=PAPER, bold=True) + 3
        for mark in marks:
            symbol, color = HISTORY_MARKS[mark]
            x = cv.put(x, 0, symbol + " ", fg=color)

    @staticmethod
    def shoe(cv: Canvas, L: Layout, left: int):
        for k in range(3):
            draw_card(cv, L.shoe_x + k, L.dealer, None)
        cv.center(L.shoe_x + 6, L.dealer + 5, f"шуз {left}", fg=FAINT)

    @staticmethod
    def intro(cv: Canvas, game: Game, L: Layout):
        styles = {"title": (GOLD, True), "text": (CREAM, False), "note": (FADED, False)}
        items = intro_items(game, TABLE_W - 8) + [
            ("", "text"), ("Ставку выберите стрелками ← → или наберите цифрами, Enter — раздать.", "note")]
        for y, (text, kind) in enumerate(items, start=L.dealer):
            fg, bold = styles[kind]
            cv.put(L.ox + 4, y, text, fg=fg, bold=bold)

    @staticmethod
    def label(cv: Canvas, cx, y, name, badge, width, bet=None, active=False):
        """Подпись места над картами: имя, сумма очков, фишки ставки."""
        chips = chip_colors(bet, 5 if width >= 30 else 3) if bet else []
        total = text_width(name) + (text_width(badge[0]) + 3 if badge else 0)
        if bet:
            total += 3 + len(chips) + len(money(bet))
        x = cv.put(cx - total // 2, y, name, fg=GOLD if active else CREAM, bold=True)
        if badge:
            bg, fg = BADGES[badge[1]]
            x = cv.put(x + 1, y, f" {badge[0]} ", fg=fg, bg=bg, bold=True)
        if bet:
            x += 2
            for color in chips:
                x = cv.put(x, y, "◉", fg=color)
            cv.put(x + 1, y, money(bet), fg=CREAM, bold=True)

    @staticmethod
    def result(game: Game):
        """Баннер итога: (текст, вид) — или None, пока раздача идёт."""
        if not game.hands or not all(hand.outcome for hand in game.hands):
            return None
        net = sum(hand.net for hand in game.hands)
        if len(game.hands) == 1:
            kind = game.hands[0].outcome
            text = OUTCOMES[kind][0].upper()
        else:
            kind = "win" if net > 0 else "lose" if net < 0 else "push"
            text = "ИТОГ" if net else "НИЧЬЯ"
        return (f"{text}  {signed(net)}" if net else text), kind

    @staticmethod
    def banner(cv: Canvas, L: Layout, text, kind):
        bg, fg = BADGES[kind]
        body = f"   ★  {text}  ★   "
        x, y = L.cx - text_width(body) // 2, L.table + 1
        cv.put(x, y - 1, "▄" * text_width(body), fg=bg)
        cv.put(x, y, body, fg=fg, bg=bg, bold=True)
        cv.put(x, y + 1, "▀" * text_width(body), fg=bg)

    # ── анимации ──

    def animate(self, game: Game, L: Layout, bar):
        """Доносит из шуза карты, появившиеся с прошлого кадра, и переворачивает
        закрытую карту дилера, когда он её открыл."""
        if self.seen_round != game.rounds:
            self.seen_round, self.seen, self.hole_revealed, self.buttons = game.rounds, {}, False, None
        arrivals = []
        for hand in [game.dealer] + game.hands:
            # у новой руки после сплита первая карта не из шуза, а из соседней руки
            before = self.seen.get(id(hand), len(hand.cards) if hand.split else 0)
            arrivals += [(hand, i) for i in range(before, len(hand.cards))]
            self.seen[id(hand)] = len(hand.cards)
        for hand, index in arrivals:
            self.slide(game, L, hand, index, bar)
        if len(game.dealer.cards) > 1 and not game.hole_hidden and not self.hole_revealed:
            self.hole_revealed = True
            self.flip(game, L, bar)

    def slide(self, game: Game, L: Layout, hand: Hand, index: int, bar):
        tx, ty = self.card_xy(game, L, hand, index)
        sx, sy = L.shoe_x + 2, L.dealer
        face_down = hand is game.dealer and index == 1 and game.hole_hidden
        card = None if face_down else hand.cards[index]
        for frame in range(1, SLIDE_FRAMES + 1):
            t = 1 - (1 - frame / SLIDE_FRAMES) ** 3  # к концу пути карта замедляется
            cv = self.table(game, L, skip=(hand, index))
            draw_card(cv, round(sx + (tx - sx) * t), round(sy + (ty - sy) * t), card, L.big)
            bar(cv)
            self.flush(cv)
            time.sleep(FRAME_TIME)

    def flip(self, game: Game, L: Layout, bar):
        for width, face_up in ((L.card_w, False), (5, False), (1, False), (5, True)):
            cv = self.table(game, L, flip=(width, face_up))
            bar(cv)
            self.flush(cv)
            time.sleep(0.25 if width == L.card_w else 0.06)

    # ── то, что вызывает игра ──

    def show(self, game: Game, delay=0.0):
        if game.active is not None and self.buttons:
            items = self.buttons
            self.render(game, lambda cv: keycap_bar(cv, items))
        else:
            status = "ход дилера…" if not game.hole_hidden else "раздача…"
            self.render(game, lambda cv: text_bar(cv, [(status, MUTED, None, False)]))
        if delay:
            time.sleep(delay)

    def choose(self, game: Game, hand: Hand, actions) -> str:
        hint = self.hints
        while True:
            best, ratings = hint_ratings(game, hand, actions, self.hint_style) if hint else (None, {})
            name, about = HINT_STYLES[self.hint_style]
            items = [(key.upper(), label, "best" if key == best else "on" if key in actions else "off",
                      ratings.get(key)) for key, label in ACTIONS.items()]
            items += [("T", "вид", "on", (name, "plain")) if hint else ("?", "совет", "on", None),
                      ("Q", "выход", "on", None)]
            self.buttons = items
            self.render(game, lambda cv: keycap_bar(cv, items), f"💡 {name} — {about}" if hint else None)
            key = KEYMAP.get(self.kb.key().lower())
            if key in actions:
                return key
            if key == "?":
                hint = True
            elif key == "t":  # следующий вид совета — и сразу показать его
                self.next_hint_style()
                hint = True
            elif key == "q" and self.confirm(game, "Выйти из игры? Ставка на столе сгорит."):
                raise Quit

    def confirm(self, game: Game, question: str) -> bool:
        gap = [("    ", None, None, False)]
        while True:
            self.render(game, lambda cv: text_bar(cv, [(question, CREAM, None, True)] + gap
                                                  + cap("Y", "да") + gap + cap("N", "нет")))
            key = KEYMAP.get(self.kb.key().lower())
            if key in ("y", "n"):
                return key == "y"

    def ask_bet(self, game: Game) -> int:
        """Ставка кнопками: ← → по шагам, цифры — своя сумма, Enter — раздать."""
        bet, typing, error = min(self.last_bet, int(game.bank)), False, None
        while True:
            self.render(game, lambda cv: self.bet_bar(cv, game, bet, error))
            key, error = self.kb.key(), None
            steps = [step for step in BET_STEPS if step < game.bank] + [int(game.bank)]
            if key in ("right", "up"):
                bet, typing = next((s for s in steps if s > bet), bet), False
            elif key in ("left", "down"):
                bet, typing = next((s for s in reversed(steps) if s < bet), bet), False
            elif key and key in "0123456789":
                bet, typing = min(int(f"{bet if typing else ''}{key}"), int(game.bank)), True
            elif key == "backspace":
                bet, typing = bet // 10, True
            elif KEYMAP.get(key.lower()) == "enter":
                if bet >= 1:
                    self.last_bet = bet
                    return bet
                error = "Ставка — хотя бы 1"
            elif KEYMAP.get(key.lower()) == "q":
                raise Quit

    @staticmethod
    def bet_bar(cv: Canvas, game: Game, bet, error=None):
        gap = [("      ", None, None, False)]
        text_bar(cv, cap("←→", "ставка") + [(f"  ◀ {money(bet)} ▶", GOLD, None, True)] + gap
                 + cap("⏎", "раздать", "best") + gap + cap("Q", "выход"))
        if error:
            below = [(error, TONES["bad"], None, True)]
        else:
            below = [("◉", color, None, False) for color in chip_colors(bet)] + [(
                f"  банк {money(game.bank)} · за сессию {signed(game.bank - game.start_bank)}"
                " · сумму можно набрать цифрами", MUTED, None, False)]
        draw_segments(cv, cv.h - 1, below)

    def game_over(self, game: Game) -> bool:
        gap = [("      ", None, None, False)]
        while True:
            self.render(game, lambda cv: text_bar(cv, cap("⏎", "начать заново", "best") + gap + cap("Q", "выход")),
                        banner=("БАНК ПУСТ", "lose"))
            key = KEYMAP.get(self.kb.key().lower())
            if key in ("enter", "q"):
                return key == "enter"


def main():
    parser = argparse.ArgumentParser(description="Блэкджек в терминале.")
    parser.add_argument("--dealer", choices=DEALERS, default="smart",
                        help="smart — умный дилер (по умолчанию); s17 и h17 — по правилам казино")
    parser.add_argument("--decks", type=int, default=6, help="колод в шузе, 1–8 (по умолчанию 6)")
    parser.add_argument("--bank", type=int, default=1000, help="стартовый банк (по умолчанию 1000)")
    parser.add_argument("--hints", action="store_true", help="показывать совет на каждом ходу")
    parser.add_argument("--hint-style", choices=HINT_STYLES, default="words",
                        help="вид совета: words — словами (по умолчанию), odds — шансы, "
                             "ev — матожидание; в игре меняется клавишей T")
    parser.add_argument("--classic", action="store_true",
                        help="прежний интерфейс без сукна — для терминалов без 256 цветов")
    args = parser.parse_args()
    if not 1 <= args.decks <= 8:
        parser.error("--decks: от 1 до 8")
    if args.bank < 1:
        parser.error("--bank: хотя бы 1")

    if os.name == "nt":
        os.system("")  # включает ANSI-цвета в консоли Windows
    screen = sys.stdout.isatty()
    felt = screen and sys.stdin.isatty() and COLOR and not args.classic
    with Keyboard() as kb:
        ui = (FeltUI if felt else TerminalUI)(kb, hints=args.hints, hint_style=args.hint_style)
        game = Game(ui, args.dealer, args.decks, args.bank)
        if screen:
            sys.stdout.write("\033[?1049h\033[?25l")  # отдельный экран, без курсора
        try:
            while True:
                if game.bank < 1:
                    if not ui.game_over(game):
                        break
                    game.reset()
                game.play_round(ui.ask_bet(game))
        except (Quit, KeyboardInterrupt):
            pass
        finally:
            if screen:
                sys.stdout.write("\033[?25h\033[?1049l")
                sys.stdout.flush()
    print(f"Раздач: {game.rounds} · банк: {money(game.bank)} ({signed(game.bank - game.start_bank)}). До встречи! 🃏")


if __name__ == "__main__":
    main()
