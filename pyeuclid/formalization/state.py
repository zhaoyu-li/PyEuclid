import os
import sys
import logging

from collections import defaultdict
from itertools import permutations
from typing import Iterable

from pyeuclid.formalization.utils import *
from pyeuclid.formalization.translation import *
from pyeuclid.formalization.diagram import *
from pyeuclid.formalization.relation import *


class State:
    def __init__(self):
        self.goal = None
        self.diagram = None
        self.points = set()
        self.relations = set()
        self.equations = set()
        self.lengths = UnionFind()
        self.angles = UnionFind()
        self.var_types = {}
        self.ratios = {}
        self.angle_sums = {}
        self.point2constructions = defaultdict(list)
        self.depth2conditions = defaultdict(list)
        self.condition2depth = defaultdict(int)
        
        self.current_depth = 0
        self.solutions = {}
        self.solvers = {}
        self.try_complex = False
        self.silent = False
        self.logger = logging.getLogger(__name__)
        self.set_logger(logging.DEBUG)
        
    def load_problem(self, conditions=None, goal=None, diagram=None):        
        if conditions:
            self.add_conditions(conditions)
            old_size = 0
            self.categorize_variable()
            size = len(self.var_types)
            while(size > old_size):
                self.categorize_variable()
                old_size = size
                size = len(self.var_types)
        if goal:
            self.goal = goal
        if diagram:
            self.diagram = diagram
    
    def set_logger(self, level):
        self.logger.setLevel(level)
        rank = os.environ.get("OMPI_COMM_WORLD_RANK", None)
        if not len(self.logger.handlers):
            handler = logging.StreamHandler(sys.stdout)
            if rank is None:
                formatter = logging.Formatter(
                    '%(levelname)s - %(message)s')  # %(asctime)s - %(name)s -
            else:
                formatter = logging.Formatter(
                    rank+' %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            self.logger.addHandler(handler)
        
    def add_conditions(self, relations):
        if not isinstance(relations, Iterable):
            relations = [relations]
        for item in relations:
            if isinstance(item, Relation):
                if self.diagram is not None:
                    assert self.diagram.numerical_check(item)
                self.add_relation(item)
            else:
                if self.diagram is not None:
                    if isinstance(item, Traced):
                        assert self.diagram.numerical_check(item.expr)
                    else:
                        assert self.diagram.numerical_check(item)
                self.add_equation(item)
            
            self.depth2conditions[self.current_depth].append(item)
            self.condition2depth[item] = self.current_depth
 
    def add_relation(self, relation):
        if relation in self.relations:
            return
        points = relation.get_points()
        for p in points:
            self.add_point(p)
        self.relations.add(relation)
        
    def add_point(self, *ps):
        for p in ps:
            if not p in self.points:
                for point in self.points:
                    self.lengths.add(Length(point, p))
                    for point1 in self.points:
                        if point1 == point:
                            continue
                        self.angles.add(Angle(point1, p, point))
                        self.angles.add(Angle(p, point, point1))
                        self.angles.add(Angle(p, point1, point))
                self.points.add(p)

    def add_equation(self, equation):
        # allow redundant equations for neat proofs
        equation = Traced(equation, depth=self.current_depth)
        points_list, quantities = get_points_and_symbols(equation)
        points = [p for points in points_list for p in points]
        for p in points:
            self.add_point(p)
        unionfind = None
        for quantity in quantities:
            if "Angle" in str(quantity):
                unionfind = self.angles
                unionfind.add(quantity)
            elif "Length" in str(quantity):
                unionfind = self.lengths
                unionfind.add(quantity)
        
        # trival equations
        if str(equation) == '0':
            return
        
        negated = Traced(-equation.expr)
        if equation not in self.equations and negated not in self.equations:
            self.equations.add(equation)
    
    def categorize_variable(self):
        angle_linear, length_linear, length_ratio, others = classify_equations(self.equations, self.var_types)
        for eq in self.equations:
            if "Variable" not in str(eq):
                continue
            _, entities = get_points_and_symbols(eq)
            label = None
            if eq in angle_linear and ("Angle" in str(eq) or "pi" in str(eq)):
                label = "Angle"
            elif eq in length_linear and "Length" in str(eq):
                label = "Length"
            elif eq in length_ratio and "Length" in str(eq):
                label = "Length"
            else:
                continue
            for entity in entities:
                if label is not None:
                    if entity in self.var_types:
                        if self.var_types[entity] is None: # dimensionless variable
                            continue
                        elif self.var_types[entity] != label:
                            self.var_types[entity] = None
                    else:
                        self.var_types[entity] = label
    
    def add_constructions(self, constructions):
        for construction in constructions:
            for p in construction.outputs:
                self.add_point(p)
                self.point2constructions[p].append(construction)
                
            relations = construction.conclusions()

            for relation in relations:
                # if isinstance(relation, tuple):
                #     if self.diagram.numerical_check(relation[0]):
                #         assert not self.diagram.numerical_check(relation[1])
                #         relation = relation[0]
                #     else:
                #         assert self.diagram.numerical_check(relation[1])
                #         relation = relation[1]
                
                if isinstance(relation, sympy.core.expr.Expr):
                    relation = Traced(relation)
                    relation.sources = [construction]
                else:
                    relation.source = construction
                
                self.add_conditions(relation)
        
        for perm in permutations(self.points, 3):
            between_relation = Between(*perm)
            if self.diagram.numerical_check(between_relation):
                self.add_conditions(between_relation)
                
            notcollinear_relation = Not(Collinear(*perm))
            if self.diagram.numerical_check(notcollinear_relation):
                self.add_conditions(notcollinear_relation)
        
        for perm in permutations(self.points, 4):
            sameside_relation = SameSide(*perm)
            if self.diagram.numerical_check(sameside_relation):
                self.add_conditions(sameside_relation)
                
            oppositeside_relation = OppositeSide(*perm)
            if self.diagram.numerical_check(oppositeside_relation):
                self.add_conditions(oppositeside_relation)
        
    def load_problem_from_text(self, text, diagram_path=None, resample=False):
        constructions_list = get_constructions_list_from_text(text)
        goal = get_goal_from_text(text)
        satisfied_goal = None
        
        diagram = Diagram(constructions_list, diagram_path, resample=resample)

        if goal:
            satisfied, satisfied_goal = diagram.numerical_check_goal(goal)
            
            for _ in range(MAX_DIAGRAM_ATTEMPTS):
                if satisfied:
                    break
                diagram = Diagram(constructions_list, diagram_path, resample=True)
                satisfied, satisfied_goal = diagram.numerical_check_goal(goal)

            if not satisfied:
                raise Exception(f"Failed to satisfy goal after {MAX_DIAGRAM_ATTEMPTS} attempts.")
        
        self.diagram = diagram
        self.goal = satisfied_goal
        goal_constructions = get_constructions_from_goal(satisfied_goal)
        self.diagram.draw([], goal_constructions)
        self.diagram.draw_diagram()
        
        for constructions in constructions_list:
            self.add_constructions(constructions)
 
    def complete(self):
        if not self.goal:
            return None
        
        if isinstance(self.goal, Relation):
            if self.check_conditions(self.goal):
                return True
            else:
                return None
        else:
            assert isinstance(self.goal, sympy.core.expr.Expr)
            solution = self.simplify_equation(self.goal)
            if len(solution.free_symbols) == 0:
                return solution
            return None
    
    def simplify_equation(self, expr):
        solved_vars = self.solutions
        expr = getattr(expr, "expr", expr)
        for symbol in expr.free_symbols:
            if symbol in solved_vars:
                value = solved_vars[symbol]
                expr = expr.subs(symbol, value)
        return expr
    
    def check_conditions(self, conditions):
        if not type(conditions) in (list, tuple, set):
            conditions = [conditions]
        conditional_relations, conditional_equations = set(), []
        i = 0
        while i < len(conditions):
            item = conditions[i]
            if isinstance(item, Different2):
                if item.negated is True:
                    return False
            # auxillary predicate for canonical ordering of inference rule params, does not used for checking
            elif isinstance(item, Lt):
                pass
            elif isinstance(item, Between):
                if item.negated:
                    if Not(item) in self.relations:
                        return False
                else:
                    if not item in self.relations:
                        return False
                    if item.p1 == item.p2 or item.p2 == item.p3 or item.p3 == item.p1:
                        return False
            elif isinstance(item, Relation):
                if isinstance(item, Collinear) and (item.p1 == item.p2 or item.p2 == item.p3 or item.p3 == item.p1):
                    if item.negated:
                        return False
                elif not item in self.relations:
                    return False
            else:
                conditional_equations.append(self.simplify_equation(item))
            i += 1
        equation_satisfied = check_equalities(conditional_equations)
        return equation_satisfied
    