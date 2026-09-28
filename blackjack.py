#!/usr/bin/env python3
"""Блэкджек в терминале.

    python3 blackjack.py                  # умный дилер, 6 колод, банк 1000
    python3 blackjack.py --dealer s17     # дилер по правилам казино
    python3 blackjack.py --hints          # совет на каждом ходу
    python3 blackjack.py --help           # все настройки

Управление: H — ещё, S — хватит, D — удвоить, P — разделить, ? — совет, Q — выход.
Клавиши работают и в русской раскладке. Зависимостей нет, нужен Python 3.9+.
"""

from __future__ import annotations

import argparse
import os
import random
import shutil
import sys
import textwrap
import time
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

def advise(hand: Hand, up: Card, mode: str, counts, actions) -> dict[str, float]:
    """Средний результат каждого действия в долях ставки (+0.1 — это +10 %).

    Считается для текущей руки так, будто она одна, по составу оставшегося
    шуза, но без учёта того, что карты уходят по ходу раздачи."""
    n = sum(counts)
    p = [k / n for k in counts]
    # Блэкджека у дилера нет — он уже проверил закрытую карту
    hole = [0.0 if (up.value == 1 and i == 9) or (up.value == 10 and i == 0) else q
            for i, q in enumerate(p)]
    hole = [q / sum(hole) for q in hole]

    @lru_cache(maxsize=None)
    def dealer_plays(hard, has_ace, t):
        """Результат игрока с суммой t, пока дилер доигрывает свою руку."""
        total = best_total(hard, has_ace)
        now = (t > total) - (t < total)
        if mode == "smart":
            done = total == 21
        else:
            done = total > 17 or total == 17 and not (mode == "h17" and total != hard)
        if done:
            return now
        hit = sum(q * (1 if hard + i + 1 > 21 else dealer_plays(hard + i + 1, has_ace or i == 0, t))
                  for i, q in enumerate(p) if q)
        return min(now, hit) if mode == "smart" else hit

    @lru_cache(maxsize=None)
    def stand_ev(t):
        return sum(q * dealer_plays(up.value + i + 1, up.value == 1 or i == 0, t)
                   for i, q in enumerate(hole) if q)

    def stand_on(hard, has_ace):
        return stand_ev(best_total(hard, has_ace))

    def after_card(hard, has_ace, then):
        """Средний результат после ещё одной карты; перебор — минус ставка."""
        return sum(q * (-1 if hard + i + 1 > 21 else then(hard + i + 1, has_ace or i == 0))
                   for i, q in enumerate(p) if q)

    @lru_cache(maxsize=None)
    def play_on(hard, has_ace):
        """Лучший результат, если дальше можно и брать, и остановиться."""
        now = stand_on(hard, has_ace)
        if best_total(hard, has_ace) == 21:
            return now
        return max(now, after_card(hard, has_ace, play_on))

    def double_on(hard, has_ace):
        return 2 * after_card(hard, has_ace, stand_on)

    ev = {"h": after_card(hand.hard, hand.has_ace, play_on), "s": stand_on(hand.hard, hand.has_ace)}
    if "d" in actions:
        ev["d"] = double_on(hand.hard, hand.has_ace)
    if "p" in actions:
        value = hand.cards[0].value
        if value == 1:  # тузы после сплита получают по одной карте
            one = after_card(1, True, stand_on)
        else:
            one = after_card(value, False, lambda h, a: max(play_on(h, a), double_on(h, a)))
        ev["p"] = 2 * one
    return ev


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
        if len(self.hands) > 1:
            self.messages.append("Итог раздачи: " + signed(sum(h.net for h in self.hands)))


# ─── Отрисовка ───────────────────────────────────────────────────────────

COLOR = sys.stdout.isatty() and "NO_COLOR" not in os.environ
BOLD, DIM, RED, GREEN, YELLOW, BLUE, CYAN = "1", "2", "31", "32", "33", "34", "36"

ACTIONS = {"h": "ещё", "s": "хватит", "d": "удвоить", "p": "разделить"}
OUTCOMES = {
    "blackjack": ("блэкджек", YELLOW),
    "win": ("победа", GREEN),
    "push": ("ничья", YELLOW),
    "lose": ("проигрыш", RED),
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


def chips(x) -> str:
    """Средний выигрыш в фишках: +3.0 зелёным, −2.1 красным."""
    digits = 2 if abs(x) < 1 else 1 if abs(x) < 10 else 0
    if not round(x, digits):
        return paint("0", DIM)
    return paint(f"{x:+.{digits}f}".replace("-", "−"), GREEN if x > 0 else RED)


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


def intro_lines(game: Game, width: int) -> list[str]:
    name, about = DEALERS[game.mode]
    rules = [
        "блэкджек платит 3:2, при ничьей ставка возвращается",
        "если у дилера открыт туз или десятка, он сразу проверяет, нет ли у него блэкджека",
        "удвоить можно на любых двух картах, в том числе после сплита",
        f"пару можно разделить, всего до {MAX_HANDS} рук; тузы после сплита получают по одной карте",
        f"дилер {name}: {about}",
        "совет (?) показывает, сколько фишек в среднем приносит каждый ход; "
        "минус значит, что в среднем вы теряете",
    ]
    lines = ["", "  Сделайте ставку, чтобы начать.", "", paint("  Правила", BOLD)]
    for rule in rules:
        lines += textwrap.wrap(rule, width - 2, initial_indent="  • ", subsequent_indent="    ")
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


def controls(actions) -> str:
    items = [f"{key_label(a.upper())} {name}" for a, name in ACTIONS.items() if a in actions]
    items += [f"{key_label('?')} совет", f"{key_label('Q')} выход"]
    return "  " + "   ".join(items)


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
    "?": "?", "/": "?", ",": "?", ".": "?",
    "\n": "enter", "\r": "enter", " ": "enter",
}


class Keyboard:
    """Нажатия без Enter: на время игры терминал переводится в режим cbreak.
    Если ввод не терминал (например, pipe), читаем построчно."""

    def __init__(self):
        self.fd = sys.stdin.fileno() if termios and sys.stdin.isatty() else None
        self.saved = None

    def __enter__(self):
        if self.fd is not None:
            self.saved = termios.tcgetattr(self.fd)
            tty.setcbreak(self.fd)
        return self

    def __exit__(self, *exc):
        if self.saved is not None:
            termios.tcsetattr(self.fd, termios.TCSADRAIN, self.saved)

    def key(self) -> str:
        if self.fd is not None:
            termios.tcflush(self.fd, termios.TCIFLUSH)  # нажатия во время анимации не в счёт
            data = os.read(self.fd, 16)
            if data.startswith(b"\x1b"):  # стрелки и прочие спецклавиши
                return ""
            return data.decode("utf-8", "ignore")[:1]
        if os.name == "nt" and sys.stdin.isatty():
            import msvcrt
            return msvcrt.getwch()
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
    def __init__(self, keyboard: Keyboard, hints=False):
        self.kb = keyboard
        self.hints = hints
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
        hint = self.hint(game, hand, actions) if self.hints else []
        while True:
            self.show(game, footer=hint + [controls(actions)])
            key = KEYMAP.get(self.kb.key().lower())
            if key in actions:
                return key
            if key == "?":
                hint = self.hint(game, hand, actions)
            elif key == "q" and self.confirm(game, "Выйти из игры? Ставка на столе сгорит."):
                raise Quit

    def hint(self, game: Game, hand: Hand, actions) -> list[str]:
        """Лучший ход и сколько фишек в среднем приносит каждый ход при текущей ставке."""
        ev = advise(hand, game.dealer.cards[0], game.mode, game.shoe.counts(), actions)
        ranked = sorted(ev, key=ev.get, reverse=True)
        details = " · ".join(f"{ACTIONS[a]} {chips(ev[a] * hand.bet)}" for a in ranked)
        return [f"  💡 Совет: {paint(ACTIONS[ranked[0]].upper(), BOLD, YELLOW)}",
                f"     {paint('в среднем за раздачу:', DIM)} {details}"]

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


def main():
    parser = argparse.ArgumentParser(description="Блэкджек в терминале.")
    parser.add_argument("--dealer", choices=DEALERS, default="smart",
                        help="smart — умный дилер (по умолчанию); s17 и h17 — по правилам казино")
    parser.add_argument("--decks", type=int, default=6, help="колод в шузе, 1–8 (по умолчанию 6)")
    parser.add_argument("--bank", type=int, default=1000, help="стартовый банк (по умолчанию 1000)")
    parser.add_argument("--hints", action="store_true", help="показывать совет на каждом ходу")
    args = parser.parse_args()
    if not 1 <= args.decks <= 8:
        parser.error("--decks: от 1 до 8")
    if args.bank < 1:
        parser.error("--bank: хотя бы 1")

    if os.name == "nt":
        os.system("")  # включает ANSI-цвета в консоли Windows
    screen = sys.stdout.isatty()
    with Keyboard() as kb:
        ui = TerminalUI(kb, hints=args.hints)
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
