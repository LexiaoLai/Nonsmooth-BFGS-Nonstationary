#!/usr/bin/env python3
"""Exact outward intervals, two-variable first derivatives, and small matrices.

Every arithmetic result is enclosed on the grid 2**(-256). Binary floating
point inputs are rejected; use integer, Fraction, Decimal, or decimal strings.
"""
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError("Run the verifier without Python's -O option.")

BITS = 256
Q = 2**BITS


def exact(value):
    """Read a scalar without silently accepting a binary float."""
    if isinstance(value, float):
        raise TypeError("Binary floats are not certificate inputs; use a decimal string.")
    return F(value)


def lower(value):
    value = exact(value)
    return F((value.numerator * Q) // value.denominator, Q)


def upper(value):
    return -lower(-exact(value))


def decimal_bound(value, places=6, *, upward=False):
    """Fixed-place decimal rounded outwards, using integer arithmetic only."""
    if not isinstance(places, int) or places < 0:
        raise ValueError("places must be a nonnegative integer")
    value = exact(value)
    scale = 10**places
    numerator = value.numerator * scale
    integer = (-((-numerator) // value.denominator) if upward
               else numerator // value.denominator)
    sign = '-' if integer < 0 else ''
    whole, part = divmod(abs(integer), scale)
    return f'{sign}{whole}.{part:0{places}d}' if places else f'{sign}{whole}'


def decimal_down(value, places=6):
    return decimal_bound(value, places)


def decimal_up(value, places=6):
    return decimal_bound(value, places, upward=True)


class IV:
    """A closed rational interval; operations always enclose their inputs."""

    def __init__(self, a, b=None):
        if isinstance(a, IV):
            if b is not None:
                raise TypeError("A copied interval cannot have a second endpoint.")
            self.lo, self.hi = a.lo, a.hi
            return
        a, b = exact(a), exact(a if b is None else b)
        if a > b:
            raise ValueError("Interval endpoints must be ordered.")
        self.lo, self.hi = lower(a), upper(b)

    def __add__(self, b):
        if isinstance(b, Jet):
            return b + self
        b = IV(b)
        return IV(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return IV(-self.hi, -self.lo)

    def __sub__(self, b):
        return self + (-b if isinstance(b, (IV, Jet)) else -IV(b))

    def __rsub__(self, b):
        return -self + b

    def __mul__(self, b):
        if isinstance(b, Jet):
            return b * self
        b = IV(b)
        products = [x*y for x in (self.lo, self.hi) for y in (b.lo, b.hi)]
        return IV(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, b):
        if isinstance(b, Jet):
            return Jet(self) / b
        b = IV(b)
        if b.lo <= 0 <= b.hi:
            raise ZeroDivisionError("Cannot divide by an interval containing zero.")
        return self * IV(1/b.hi, 1/b.lo)

    def __rtruediv__(self, b):
        return IV(b) / self

    def mag(self):
        return max(abs(self.lo), abs(self.hi))

    def out(self):
        """Export enclosing decimal endpoints with 80 significant digits."""
        with localcontext() as context:
            context.prec = 80
            context.rounding = ROUND_FLOOR
            lo = str(Decimal(self.lo.numerator) / Decimal(self.lo.denominator))
            context.rounding = ROUND_CEILING
            hi = str(Decimal(self.hi.numerator) / Decimal(self.hi.denominator))
        if not exact(lo) <= self.lo <= self.hi <= exact(hi):
            raise ArithmeticError("Decimal export failed to enclose the interval.")
        return [lo, hi]


def format_interval(value, places=6):
    """Outward decimal display of an IV or a two-endpoint exported interval."""
    lo, hi = (value.lo, value.hi) if isinstance(value, IV) else value
    if exact(lo) > exact(hi):
        raise ValueError("Interval endpoints must be ordered.")
    return f'[{decimal_down(lo, places)}, {decimal_up(hi, places)}]'


class Jet:
    """An interval value with its two interval partial derivatives."""

    def __init__(self, v, dx=0, dy=0):
        self.v, self.dx, self.dy = IV(v), IV(dx), IV(dy)

    def __add__(self, b):
        b = b if isinstance(b, Jet) else Jet(b)
        return Jet(self.v+b.v, self.dx+b.dx, self.dy+b.dy)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.dx, -self.dy)

    def __sub__(self, b):
        return self + -(b if isinstance(b, Jet) else Jet(b))

    def __rsub__(self, b):
        return -self + b

    def __mul__(self, b):
        b = b if isinstance(b, Jet) else Jet(b)
        return Jet(self.v*b.v, self.dx*b.v+self.v*b.dx, self.dy*b.v+self.v*b.dy)

    __rmul__ = __mul__

    def __truediv__(self, b):
        b = b if isinstance(b, Jet) else Jet(b)
        denominator = b.v*b.v
        return Jet(self.v/b.v, (self.dx*b.v-self.v*b.dx)/denominator,
                   (self.dy*b.v-self.v*b.dy)/denominator)

    def __rtruediv__(self, b):
        return Jet(b) / self


def _same_length(a, b):
    if len(a) != len(b):
        raise ValueError("Vector dimensions do not agree.")


def _shape(a):
    if not a or not a[0] or any(len(row) != len(a[0]) for row in a):
        raise ValueError("Expected a nonempty rectangular matrix.")
    return len(a), len(a[0])


def dot(a, b):
    _same_length(a, b)
    return sum(x*y for x, y in zip(a, b))


def add(a, b):
    _same_length(a, b)
    return [x+y for x, y in zip(a, b)]


def sub(a, b):
    _same_length(a, b)
    return [x-y for x, y in zip(a, b)]


def scale(a, t):
    return [x*t for x in a]


def mv(a, b):
    if _shape(a)[1] != len(b):
        raise ValueError("Matrix and vector dimensions do not agree.")
    return [dot(row, b) for row in a]


def outer(a, b):
    return [[x*y for y in b] for x in a]


def tr(a):
    _shape(a)
    return list(map(list, zip(*a)))


def mm(a, b):
    if _shape(a)[1] != _shape(b)[0]:
        raise ValueError("Matrix product dimensions do not agree.")
    columns = tr(b)
    return [[dot(row, col) for col in columns] for row in a]


def ma(a, b):
    if _shape(a) != _shape(b):
        raise ValueError("Matrix sum dimensions do not agree.")
    return [add(x, y) for x, y in zip(a, b)]


def ms(a, t):
    _shape(a)
    return [scale(row, t) for row in a]


def eye(n):
    if not isinstance(n, int) or n <= 0:
        raise ValueError("Matrix dimension must be a positive integer.")
    return [[IV(int(i == j)) for j in range(n)] for i in range(n)]


def pack(dx, dh):
    if len(dx) != 2 or _shape(dh) != (2, 2):
        raise ValueError("Expected a 2-vector and a 2-by-2 matrix.")
    return list(dx) + [dh[0][0], dh[0][1], dh[1][1]]


def unpack(a):
    if len(a) != 5:
        raise ValueError("Expected five tangent coordinates.")
    return a[:2], [[a[2], a[3]], [a[3], a[4]]]
