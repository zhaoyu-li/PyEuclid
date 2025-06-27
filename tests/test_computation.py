import unittest
from pyeuclid.formalization.relation import Point, Length, Angle, Lt, Collinear, Not
from pyeuclid.formalization.state import State
from pyeuclid.engine.algebraic_system import AlgebraicSystem 
from pyeuclid.engine.deductive_database import DeductiveDatabase
from pyeuclid.engine.inference_rule import InferenceRule, inference_rule_sets
from pyeuclid.engine.proof_generator import ProofGenerator
from pyeuclid.engine.engine import Engine
import sympy

a, b, c, d, e, f, g, h = Point("a"), Point("b"), Point("c"), Point("d"), Point("e"), Point("f"), Point("g"), Point("h")


class Test(unittest.TestCase):
    def test_length_linear_const(self):
        state = State()
        state.add_conditions([Length(a, c)-Length(a, b)-Length(b, c), Length(a, b)-1, Length(b, c)-2])
        state.goal = Length(a, c)
        deductive_database = DeductiveDatabase(state, outer_theorems=inference_rule_sets['basic']+inference_rule_sets['complex'])
        algebraic_system = AlgebraicSystem(state)
        proof_generator = ProofGenerator(state)
        engine = Engine(state, deductive_database, algebraic_system)
        engine.run()
        result = state.complete()
        assert result == 3
        proof_generator.run()
        proof_generator.show_proof()
        
    def test_length_linear_and_ratio(self):
        state = State()
        state.add_conditions([Length(a, c)-Length(a, b)-Length(b, c), Length(a, b)/Length(b, c)-Length(a, d)/Length(b, d), Length(a, b)- Length(b, c)-1, Length(a, d)-2*Length(b, d)])
        state.goal = Length(a, c)
        deductive_database = DeductiveDatabase(state, outer_theorems=inference_rule_sets['basic']+inference_rule_sets['complex'])
        algebraic_system = AlgebraicSystem(state)
        proof_generator = ProofGenerator(state)
        engine = Engine(state, deductive_database, algebraic_system)
        engine.run()
        result = state.complete()
        assert result == 3
        proof_generator.run()
        proof_generator.show_proof()
        
                        
if __name__=="__main__":
    unittest.main()