from pyeuclid.formalization.relation import *
from pyeuclid.engine.inference_rule import *
import sympy


class Engine:
    def __init__(self, state, deductive_database, algebraic_system):
        self.state = state
        self.deductive_database = deductive_database
        self.algebraic_system = algebraic_system
    
    def run(self):
        self.deductive_database.inner_theorems.remove(PropertyOfTriangle)
        self.search()
        if self.state.complete() is not None:
            return
        self.deductive_database.inner_theorems.append(PropertyOfTriangle)
        self.search()
        
    def search(self, depth=9999):
        self.algebraic_system.run()
        while self.state.current_depth < depth:
            if self.state.complete() is not None:
                break
                        
            closure = self.deductive_database.run()
            
            if self.state.complete() is not None or closure:
                break
            
            self.algebraic_system.run()
    
    def step(self, conditions, conclusions=[], depth=1):
        """
        Only considers a subset of points and conditions
        """
        assert len(conditions) > 0
        relations_bak = self.state.relations
        equations_bak = self.state.equations
        lengths_bak = self.state.lengths
        angles_bak = self.state.angles
        points_bak = self.state.points
        
        try:
            self.algebraic_system.solve_equation()
            for condition in conditions:
                if not self.state.check_conditions(condition):
                    raise Exception(f"Condition {condition} is not verified")
            
            self.state.equations = []
            self.state.relations = set()

            self.state.add_conditions(conditions) # this method supports both equations and relations
            for relation in relations_bak:
                if type(relation) in (Between, SameSide) or type(relation) == Collinear and relation.negated:
                    if all([point in self.state.points for point in relation.get_points()]):
                        self.state.add_relation(relation)
                
            self.search(depth=depth)
            
            for conclusion in conclusions:
                if not self.state.check_conditions(conclusion):
                    raise Exception(f"Conclusion {conclusion} is not verified")
                
            self.state.points = points_bak
            self.state.lengths = lengths_bak
            self.state.angles = angles_bak
            new_relations = [item for item in self.state.relations if not item in conditions]
            new_equations = [item for item in self.state.equations if not item in conditions]
            self.state.relations = relations_bak
            self.state.equations = equations_bak
            self.state.add_conditions(new_relations + new_equations)
            self.algebraic_system.solve_equation()
        
        except Exception as e:
            self.state.points = points_bak
            self.state.lengths = lengths_bak
            self.state.angles = angles_bak
            self.state.relations = relations_bak
            self.state.equations = equations_bak
            raise e
        return new_relations + new_equations
    