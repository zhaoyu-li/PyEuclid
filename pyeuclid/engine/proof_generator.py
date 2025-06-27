import math
import gurobipy as gp
import numpy as np
import sympy

from pyscipopt import Model, quicksum
from collections import defaultdict

from pyeuclid.formalization.relation import *
from pyeuclid.formalization.construction_rule import *
from pyeuclid.formalization.utils import *
from pyeuclid.engine.inference_rule import *


class ProofGenerator:
    def __init__(self, state, verbose=False):
        self.state = state
        self.visited = set()
        self.proof_dict = {}
        self.source_constructions = defaultdict(list)
        self.verbose = verbose
    
    def run(self, node=None, depth=None, root=True):
        if not node and self.state.goal:
            node = self.state.goal - self.state.complete()

        if isinstance(node, ConstructionRule):
            return
        
        if node in self.visited:
            return
        self.visited.add(node)

        if root:
            depth = self.state.current_depth
        
        if depth is None:
            depth = node.depth
        
        if isinstance(node, InferenceRule):
            expr_conds = set()
            for cond in node.condition():
                if isinstance(cond, sympy.core.expr.Expr):
                    expr_conds.add(str(sympy.simplify(cond)))
                    expr_conds.add(str(sympy.simplify(-cond)))
            conds = [
                eq for eq in self.state.equations
                if eq.depth < node.depth and eq.str_rep in expr_conds
            ]

            for cond in node.condition():
                if not isinstance(cond, sympy.core.expr.Expr) and not trivial_condition(cond):
                    conds.append(cond)
            self.proof_dict[node] = conds

            # conds = [item for item in node.condition() if not trivial_condition(item) and not item == 0]
            # self.proof_dict[node] = conds
            
            # print(1, 'node', node, type(node), 'depth', depth, 'sources', conds)
            for cond in conds:
                self.run(cond, depth=depth, root=False)
        elif isinstance(node, Relation):
            for tmp in self.state.relations:
                if tmp == node:
                    if hasattr(tmp, "source"):
                        source = tmp.source
                        self.proof_dict[node] = [source]
                        # print(2, 'node', node, type(node), 'depth', depth, 'sources', source)
                        self.run(source, root=False)
                    break
            else:
                assert False, f"{node} is not proved"
        else:
            if isinstance(node, Traced):
                if not node.sources or type(node.sources[0]) in (DiagramAngle4a, DiagramAngle4b, DiagramAngle2, FlatAngle, FlatAngle2):
                    sources = []
                else:
                    sources = node.sources
                    if isinstance(sources[0], str):
                        # backtrace linear systems
                        equations = [item for item in self.state.equations if item.depth < node.depth]
                        if not node.symbol is None:
                            expr = node.symbol - node.expr
                        else:
                            expr = node.expr
                        conditions = self.find_conditions(equations, expr, sources[0])
                        if not conditions:
                            breakpoint()
                            assert False
                        sources = conditions
                    else:
                        # inference rules derived
                        pass
            else:
                assert isinstance(node, sympy.core.expr.Expr)
                sources = []
                equations = [item for item in self.state.equations if item.depth < depth]
                if "Angle" in str(node):
                    conditions = self.find_conditions(equations, node, "angle_linear")
                else:
                    for tmp in ("length_ratio", "length_linear"):
                        conditions = self.find_conditions(equations, node, tmp)
                        if conditions:
                            break
                if not conditions:
                    breakpoint()
                    assert False
                sources = conditions
            self.proof_dict[node] = sources
            # print(3, 'node', node, type(node), 'depth', depth, 'sources', sources)
            for item in sources:
                self.run(item, root=False)
        
        if root and self.verbose:
            self.show_proof()

    def track_constructions(self, condition=None):
        if not condition and self.state.goal:
            condition = self.state.goal
            
        def collect(node):
            if node in self.source_constructions:
                return self.source_constructions[node]

            if isinstance(node, ConstructionRule):
                return [node]

            if node in self.proof_dict:
                constructions = set()
                for child in self.proof_dict[node]:
                    child_constructions = collect(child)
                    constructions.update(child_constructions)
                
                self.source_constructions[node] = sorted(constructions, key=lambda c: c.index)
                return self.source_constructions[node]
            
            return []
        
        collect(condition)
    
    def format_proof(self, conclusion=None):
        proof = []
        proof_steps = {}
        visited = set()
        step_counter = 1

        def search(node):  # root-last traversal
            # print('searching', node)
            nonlocal step_counter
            if node in visited or node not in self.proof_dict:
                return
            visited.add(node)
            conditions = self.proof_dict[node]
            theorem = None
            if len(conditions) == 1 and isinstance(conditions[0], InferenceRule):
                theorem = conditions[0]
                conditions = self.proof_dict[conditions[0]]
            # if len(conditions) == 1 and conditions[0] in self.proof_dict: # collapse single-condition inferences
            #     if isinstance(conditions[0], InferenceRule) and not type(conditions[0]) in inference_rule_sets["ex"]:
            #         theorem = conditions[0]
            #     conditions = self.proof_dict[conditions[0]]
            for condition in conditions:
                assert condition is not None
                search(condition)
            
            if all([type(item) in (Collinear, Between, SameSide) for item in conditions]):
                return
            # print('node', node, 'step_counter', step_counter, 'conditions', conditions)
            proof_steps[node] = (step_counter, conditions, theorem)
            step_counter += 1

        if not conclusion and self.state.goal:
            conclusion = self.state.goal

        search(conclusion)
        lst = [(key, value) for key, value in proof_steps.items()]
        lst.sort(key=lambda x: x[1][0])
        last = -1
        for node, (step_number, conditions, theorem) in lst:
            if step_number == last:
                continue
            last = step_number
            dic = {"condition": conditions, "theorem": theorem, "conclusion": node}
            proof.append(dic)
        
        return proof

    def show_proof(self, node=None):
        # print(self.proof_dict)
        res = self.get_proof_str(node)
        print(res)

    def get_proof_str(self, node=None):
        res = "Solution:\n"
        proof = self.get_proof(node)
        for step, (condition, theorem, conclusion) in enumerate(proof):
            theorem_str = ' [' + str(theorem) + ']' if theorem else ''
            res += f'{step+1}. ' + ' & '.join([str(item) for item in condition]) + theorem_str + ' => ' + str(conclusion) + '\n'
        return res
    
    def get_proof(self, node=None):
        res = []
        if not node and self.state.goal:
            node = self.state.goal - self.state.complete()
        
        proof_steps = self.format_proof(node)
        
        for proof_step in proof_steps:
            if not isinstance(proof_step['condition'][0], ConstructionRule):
                res.append(([item for item in proof_step['condition'] if not trivial_condition(item)], proof_step['theorem'], proof_step['conclusion']))
        return res

    def traceback_l1(self, augmented_A, e, threshold=1e-6):
        m, n = augmented_A.shape
        e = e[0]
        n = n - 1

        model = Model()
        model.setParam('display/verblevel', 0)

        x_pos = {}
        x_neg = {}
        for i in range(m):
            x_pos[i] = model.addVar(lb=0.0, vtype="C", name=f"x_pos_{i}")
            x_neg[i] = model.addVar(lb=0.0, vtype="C", name=f"x_neg_{i}")

        model.setObjective(
            quicksum(x_pos[i] + x_neg[i] for i in range(m)),
            sense="minimize"
        )

        for i in range(n + 1):
            model.addCons(
                quicksum(augmented_A[j, i] * (x_pos[j] - x_neg[j]) for j in range(m)) == e[i]
            )

        model.optimize()
        x_values = [model.getVal(x_pos[i]) - model.getVal(x_neg[i]) for i in range(m)]
        indices = [i for i, val in enumerate(x_values) if abs(val) > threshold]

        return indices

    def traceback_l0(self, augmented_A, e) -> list[str]:
        m, n = augmented_A.shape
        e = e[0]
        n = n - 1

        model = Model()
        model.setParam('display/verblevel', 0)

        x = {}
        z = {}
        for i in range(m):
            x[i] = model.addVar(lb=-model.infinity(), ub=model.infinity(), vtype="C", name=f"x_{i}")
            z[i] = model.addVar(vtype="B", name=f"z_{i}")

        model.setObjective(quicksum(z[i] for i in range(m)), sense="minimize")

        for i in range(n + 1):
            model.addCons(quicksum(augmented_A[j, i] * x[j] for j in range(m)) == e[i])

        M = 10
        for i in range(m):
            model.addCons(x[i] <= M * z[i])
            model.addCons(x[i] >= -M * z[i])

        model.optimize()

        obj_val = model.getObjVal()

        indices = [i for i in range(m) if model.getVal(z[i]) > 1e-12]

        assert round(obj_val) == len(indices)
        
        return indices

    def vectorize(self, equations, variables, source):
        A = np.zeros(shape=(len(equations), len(variables)), dtype=np.float64)
        b = np.zeros(shape=(len(equations), 1), dtype=np.float64)
        if source in ("angle_linear", "length_linear"):
            for i, eqn in enumerate(equations):
                eqn = sympy.expand(eqn)
                assert isinstance(eqn, sympy.core.add.Add) or isinstance(eqn, sympy.core.symbol.Symbol)

                for add_arg in eqn.args:
                    if len(add_arg.args) == 0:
                        mul_args = [add_arg]
                    else:
                        assert isinstance(add_arg, sympy.core.mul.Mul)
                        mul_args = add_arg.args
                    factors = [item for item in mul_args if len(
                        item.free_symbols) == 0]
                    factor = sympy.core.mul.Mul(*factors)
                    symbols = [item for item in mul_args if len(
                        item.free_symbols) > 0]
                    if len(symbols) == 0:
                        b[i, 0] = factor.evalf()
                    else:
                        A[i, variables[symbols[0]]] = factor.evalf()
        else:
            assert source == "length_ratio"  # length=const or eqlength or eqlength ratio or lengthratio=const
            for i, eqn in enumerate(equations):
                if isinstance(eqn, sympy.core.add.Add):
                    if len(eqn.args) > 2:
                        breakpoint()
                        assert False
                    add_args = eqn.args
                else:
                    add_args = [eqn]
                for j, add_arg in enumerate(add_args):
                    if len(add_arg.args) > 0:
                        mul_args = add_arg.args
                    else:
                        mul_args = [add_arg]
                    for mul_arg in mul_args:
                        factor = (-1)**(j)
                        if isinstance(mul_arg, sympy.core.power.Pow):
                            factor *= mul_arg.args[1]
                            mul_arg = mul_arg.args[0]
                        if len(mul_arg.free_symbols) == 0:
                            b[i, 0] += factor * math.log(abs(mul_arg))
                        else:
                            symbol = list(mul_arg.free_symbols)[0]
                            A[i, variables[symbol]] += factor
        return np.concat([A, b], axis=1)

    def find_conditions(self, equations: list[Traced], conclusion, source):
        angle_linear, length_linear, length_ratio, others = classify_equations(equations, self.state.var_types)
        """Given sympified equations and conclusions, return a list of necessary conditions"""
        def try_find(equations, conclusion):
            variables = set()
            for eqn in equations:
                variables = variables.union(eqn.free_symbols)
            variables = {item: i for i, item in enumerate(list(variables))}
            mat = self.vectorize([item.expr for item in equations], variables, source)
            eq = self.vectorize([conclusion], variables, source)
            raw_deps = self.traceback_l1(mat, eq)
            return [equations[i] for i in raw_deps]
            sub_mat = mat[raw_deps]
            sub_indices = self.traceback_l0(sub_mat, eq)
            return [equations[raw_deps[i]] for i in sub_indices]
        
        if source == "angle_linear":
            equations = angle_linear
        elif source == "length_linear":
            equations = length_linear
        else:
            assert source == "length_ratio"
            equations = length_ratio
        return try_find(equations, conclusion)
    
    def find_end_nodes(self):
        nodes_with_dependents = set()
        for sources in self.proof_dict.values():
            if sources:
                nodes_with_dependents.update(sources)

        all_nodes = set(self.proof_dict.keys())
        end_nodes = all_nodes - nodes_with_dependents
        
        return list(end_nodes)