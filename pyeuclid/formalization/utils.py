import re
import sympy
import signal

from typing import List
from pathlib import Path

ROOT_DIR = Path(__file__).parents[2]
MAX_DIAGRAM_ATTEMPTS = 1000


class TimeoutException(Exception):
    pass


class Timeout:
    def __init__(self, seconds):
        self.seconds = seconds

    def __enter__(self):
        signal.signal(signal.SIGALRM, self._handle_timeout)
        signal.setitimer(signal.ITIMER_REAL, self.seconds)

    def __exit__(self, exc_type, exc_val, exc_tb):
        signal.setitimer(signal.ITIMER_REAL, 0)  # Cancel timer
        signal.signal(signal.SIGALRM, signal.SIG_DFL)

    def _handle_timeout(self, signum, frame):
        raise TimeoutException("Operation timed out")


def sort_points(*points):
    return sorted(points, key=lambda i: i.name)

def sort_cyclic_points(*points):
    min_index = min(range(len(points)), key=lambda i: points[i].name)
    if str(points[(min_index+1) % len(points)]) > str(points[(min_index-1) % len(points)]):
        remaining_list = list(points[min_index:] + points[:min_index])[1:]
        return [points[min_index]] + remaining_list[::-1]
    else:
        return points[min_index:] + points[:min_index]


def ordered_groups(g1, g2):
    assert len(g1) == len(g2)
    for a, b in zip(g1, g2):
        if a.name != b.name:
            return a.name < b.name
    return True


def get_point_mapping(g1, g2):
    mapping = {}
    for p1, p2 in zip(g1, g2):
        mapping[p1] = p2
    return mapping


def sort_point_groups(g1, g2, mapping=False): 
    sorted_g1 = sort_points(*g1)
    sorted_g2 = sort_points(*g2)
    
    if not ordered_groups(sorted_g1, sorted_g2):
        g1, g2 = g2, g1
        sorted_g1, sorted_g2 = sorted_g2, sorted_g1
    
    if mapping:
        mapping = get_point_mapping(g1, g2)
        sorted_g2 = [mapping[p] for p in sorted_g1]
    
    return sorted_g1 + sorted_g2


class UnionFind:
    def __init__(self):
        self.parent = {}
        self.rank = {}

    def find(self, item):
        neg = getattr(item, "neg", False)
        if neg:
            item = -item
        if not item in self.parent:
            self.add(item)
            return -item if neg else item
        if self.parent[item] != item:
            self.parent[item] = self.find(self.parent[item])
        return -self.parent[item] if neg else self.parent[item]

    def union(self, item1, item2):
        if (type(item1).__name__ == 'Length' and type(item1).__name__ == 'Angle') or (type(item1).__name__ == 'Angle' and type(item1).__name__ == 'Length'):
            breakpoint()
            assert False
        root1 = self.find(item1)
        root2 = self.find(item2)
        neg = getattr(root1, "neg", False) ^ getattr(root2, "neg", False)
        if getattr(root1, "neg", False):
            root1 = - root1
        if getattr(root2, "neg", False):
            root2 = - root2
        if root1 != root2:
            if self.rank[root1] > self.rank[root2]:
                self.parent[root2] = -root1 if neg else root1
            elif self.rank[root1] < self.rank[root2]:
                self.parent[root1] = -root2 if neg else root2
            else:
                self.parent[root2] = -root1 if neg else root1
                self.rank[root1] += 1

    def add(self, item):
        if getattr(item, "neg", False):
            item = -item
        if item not in self.parent:
            self.parent[item] = item
            self.rank[item] = 0

    def equivalence_classes(self):
        dic = {}
        for item in self.parent:
            root = self.find(item)
            if root in dic:
                dic[root].append(item)
            else:
                dic[root] = [item]
        return dic

    def merge_eq(uf, v1, v2):
        uf.add(v1)
        uf.add(v2)
        uf.union(v1, v2)
        for v in [v1, v2]:
            if uf.parent[v] != v:
                v.rep_by = uf.parent[v]
                setattr(v.rep_by, "rep_by", None)


class Traced():
    def __init__(self, expr, depth=0, sources=[]):
        if isinstance(expr, Traced):
            sources = expr.sources
            depth = expr.depth
            expr = expr.expr
        
        self.expr = expr
        self.symbol = None
        self.redundant = False
        self.sources = sources
        self.str_rep = None
        self.depth = max([depth] + [getattr(item, "depth", 0) for item in self.sources])
        for key in ("free_symbols", "args"):
            setattr(self, key, getattr(self.expr, key))
    
    def subs(self, key, value):
        if isinstance(value, Traced):
            if len(self.sources) >0 and isinstance(self.sources[0], Traced):
                sources = [item for item in self.sources] + [value]
            else:
                sources = [self, value]
            value.symbol = key
            value = value.expr
        else:
            sources = self.sources
        expr = self.expr.subs(key, value)
        other = Traced(expr, sources=sources)
        other.symbol = self.symbol
        return other
    
    def __str__(self):
        # if not self.symbol is None:
        #     return str(sympy.simplify(self.symbol - self.expr))
        # else:
        #     return str(sympy.simplify(self.expr))
        if self.str_rep is None:
            if not self.symbol is None:
                self.str_rep = str(sympy.simplify(self.symbol - self.expr))
            else:
                self.str_rep = str(sympy.simplify(self.expr))
        return self.str_rep
    def __repr__(self):
        return str(self)
    def __eq__(self, other):
        return hash(self) == hash(other)
    def __hash__(self):
        return hash(str(self))

        
def infer_eq_types(eq, var_types):
    eq_types = set()
    for symbol in eq.free_symbols:
        if "Length" in str(symbol):
            eq_types.add("Length")
        elif "Angle" in str(symbol):
            eq_types.add("Angle")
        elif symbol in var_types and not var_types[symbol] is None:
            eq_types.add(var_types[symbol])
    return eq_types
    
    
def classify_equations(equations: List[Traced], var_types):
    angle_linear, length_linear, length_ratio, others = [], [], [], []
    cnst = r"(\d+|\d+\.\d*|pi)"
    cnst = f"{cnst}(\\*{cnst})*(/{cnst})*"
    length = r"(length\w+\d*|variable\w+\d*)"
    angle = r"(angle\w+\d*|variable\w+\d*)"
    length_mono = f"({cnst}\\*)?{length}(/{cnst})?"
    angle_mono = f"({cnst}\\*)?{angle}(/{cnst})?"
    length_mono = f"({length_mono}|{cnst})"
    angle_mono = f"({angle_mono}|{cnst})"
    length_ratio_pattern = re.compile(
        f"^-?{length_mono}([\\*/]{length_mono})* [+-] {length_mono}([\\*/]{length_mono})*$")
    length_linear_pattern = re.compile(
        f"^-?{length_mono}( [+-] {length_mono})+$")
    angle_linear_pattern = re.compile(
        f"^-?{angle_mono}( [+-] {angle_mono})+$")
    for i, eq in enumerate(equations):
        tmp = str(eq.expr.expand()).lower()
        eq_types = infer_eq_types(eq, var_types)
        if length_ratio_pattern.match(tmp):
            # length ratio has higher priority than length linear
            # eqratio, length eq const, eqlength, linear equations involving length and variables
            if "Length" in eq_types:
                length_ratio.append(eq)
                if length_linear_pattern.match(tmp):
                    length_linear.append(eq)
            elif "Angle" in eq_types: # such as Variable_angle_2 - piVariable_x/90
                angle_linear.append(eq)
            else:
                others.append(eq)
        elif angle_linear_pattern.match(tmp) or length_linear_pattern.match(tmp):
            # eqangle, angle eq const, angle sum
            if len(eq_types) > 1:
                breakpoint()
                assert False
            if len(eq_types) == 0:
                others.append(eq)
            elif eq_types.pop() == "Angle":
                angle_linear.append(eq)
            else:
                length_linear.append(eq)
        else:
            others.append(eq)
    return angle_linear, length_linear, length_ratio, others

def is_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


def parse_expression(expr):
    symbols = {'Angle': [], 'Length': []}
    symbol_names = {'Angle': [], 'Length': []}
    
    for arg in expr.free_symbols:
        if arg.is_Symbol:
            match1 = re.match(r'Angle_(\w+)_(\w+)_(\w+)', arg.name)
            match2 = re.match(r'Length_(\w+)_(\w+)', arg.name)
        if match1:
            symbols['Angle'].append(arg)
            symbol_names['Angle'].append(list(match1.groups()))
        if match2:
            symbols['Length'].append(arg)
            symbol_names['Length'].append(list(match2.groups()))            
            
    return symbols, symbol_names

eps = 1e-3
def is_small(x):
    if len(x.free_symbols) > 0:
        return False
    if hasattr(x, "evalf"):
        x = x.evalf()
    try:
        return abs(x) < eps
    except:
        assert False

def check_equalities(equalities):
    if not type(equalities) in (tuple, list):
        equalities = [equalities]
    for cond in equalities:
        if not (isinstance(cond, sympy.logic.boolalg.BooleanTrue) or isinstance(cond, sympy.core.numbers.Zero) or is_small(cond)):
            return False
    return True