"""
TODO
"""

from collections import defaultdict
from itertools import combinations
import textwrap

from typing import Sequence, List, Tuple, cast

import clingo
from clingox.reify import reify_program

from clingo import ast
from clingo.solving import SolveResult
from clingo.ast import ProgramBuilder
from clingo.control import Control
from clingo.application import clingo_main, Application
from clingo.propagator import PropagateControl, PropagateInit, Propagator
from clingo.backend import Backend
from clingo.ast import parse_string, parse_files, AST, ASTType
from clingox.ast import rename_symbolic_atoms

class RectangularPuzzle:
    """
    TODO
    """

    def __init__(self, width, height):
        """Initialize."""
        self.board_width = width
        self.board_height = height

        self.solution = None
        self.puzzle = None
        self.puzzle_numbers = None

        self.solving_timeout = 5

        self.domain_program = f"""
            #const board_width={self.board_width}.
            #const board_height={self.board_height}.
            row(1..board_height).
            col(1..board_width).
            cell(c(Row,Col)) :- row(Row), col(Col).
            board_height(board_height).
            board_width(board_width).
            #show board_width/1.
            #show board_height/1.

            #show puzzle/2.
            #show guessed_number/2.
            guessed_number(none,0).
            #show solution/2.
        """
        self.puzzle_gen_program = ""
        self.puzzle_constraints_program = ""
        self.solution_program = """
            1 { solution(C,V) : value(V) } 1 :- cell(C).
            solution(C,V) :- puzzle(C,V).
        """
        self.essential_solution_constraints = None

        self.naming = {}
        self.latex_naming = {}

    def pretty_name(self, value):
        if value in self.naming:
            return self.naming[value]
        if not value:
            return " "
        return value

    def latex_name(self, value):
        if value in self.latex_naming:
            return self.latex_naming[value]
        if not value:
            return " "
        return value

    def pretty_repr_puzzle(self):
        if self.puzzle:
            model_repr = '\n'.join([
                "|" + "|".join([
                    self.pretty_name(self.puzzle[(row, col)])
                    for col in range(1, self.board_width + 1)
                ]) + "|"
                for row in range(1, self.board_height + 1)
            ])
        else:
            return None
        if len(self.puzzle_numbers) > 0:
            model_repr += '\n\n' + '\n'.join([
                f"{num_name} = {self.puzzle_numbers[num_name]}"
                for num_name in self.puzzle_numbers
            ])
        return model_repr

    def latex_repr_generic(self, filling, show_numbers=True):
        if self.puzzle:
            latex_repr = textwrap.dedent(f"""
                \\begin{{tikzpicture}}[scale=1]
                  \\begin{{scope}}
                    \\draw (0,0) grid ({self.board_width},{self.board_height});
                    \\draw[ultra thick]
                      (0,0) rectangle ({self.board_width},{self.board_height});
            """)
            for row in range(1, self.board_height + 1):
                for col in range(1, self.board_width + 1):
                    x_coord = f"{self.board_height+0.5-row}"
                    y_coord = f"{col-0.5}"
                    latex_repr += "      \\node[anchor=center] "
                    latex_repr += f"({row};{col})"
                    latex_repr += " at "
                    latex_repr += f"({y_coord},{x_coord}) "
                    if filling[(row, col)]:
                        name = self.latex_name(filling[(row, col)])
                    else:
                        name = " "
                    latex_repr += f"{{{name}}};\n"
            latex_repr = latex_repr[:-1]
            latex_repr += textwrap.dedent(f"""
                  \\end{{scope}}
                \\end{{tikzpicture}}
            """)
            if show_numbers:
                if len(self.puzzle_numbers) > 0:
                    latex_repr += '\\\\\n' + ' \\quad '.join([
                        f"{self.latex_name(num_name)}: " + \
                        f"{self.puzzle_numbers[num_name]}"
                        for num_name in self.puzzle_numbers
                    ])
            return latex_repr
        return None

    def latex_repr_puzzle(self):
        return self.latex_repr_generic(self.puzzle, show_numbers=True)

    def latex_repr_solution(self):
        return self.latex_repr_generic(self.solution, show_numbers=False)

    def pretty_repr_solution(self):
        if self.solution:
            model_repr = '\n'.join([
                "|" + "|".join([
                    self.pretty_name(self.solution[(row, col)])
                    for col in range(1, self.board_width + 1)
                ]) + "|"
                for row in range(1, self.board_height + 1)
            ])
        else:
            return None
        return model_repr

    def interpret_model(
        self,
        model,
        verbose=False,
    ):
        if verbose:
            print(".", end="")
        self.puzzle = defaultdict(lambda: None)
        self.solution = defaultdict(lambda: None)
        self.puzzle_numbers = {}
        for atom in model.symbols(shown=True):
            if atom.name == "puzzle":
                row = atom.arguments[0].arguments[0].number
                col = atom.arguments[0].arguments[1].number
                value = str(atom.arguments[1])
                self.puzzle[(row, col)] = value
            elif atom.name == "solution":
                row = atom.arguments[0].arguments[0].number
                col = atom.arguments[0].arguments[1].number
                value = str(atom.arguments[1])
                self.solution[(row, col)] = value
            elif atom.name == "guessed_number":
                num_name = str(atom.arguments[0])
                num_val = atom.arguments[1].number
                if num_name != "none":
                    self.puzzle_numbers[num_name] = num_val
            elif atom.name == "print":
                print(atom)

    def generate(
        self,
        verbose=False,
        num_models=1,
        precompute_solution=False,
        use_cegar=False,
        enforce_essential_constraints=True,
        quality_check_criteria=None,
    ):
        """
        TODO
        """

        if use_cegar:
            self.generate_with_cegar(
                verbose=verbose,
                num_models=num_models,
                enforce_essential_constraints=enforce_essential_constraints
            )
            return

        essential_solution_program = ""
        reified_solution_programs = []
        if self.essential_solution_constraints:
            essential_solution_program = "".join(
                self.essential_solution_constraints
            )

            if enforce_essential_constraints:
                for i, solution_constraints in enumerate(list(map(list,
                    combinations(
                        self.essential_solution_constraints,
                        r=len(self.essential_solution_constraints)-1)
                    )
                )):
                    program_to_reify = self.domain_program
                    program_to_reify += self.puzzle_gen_program
                    program_to_reify += self.solution_program
                    program_to_reify += "".join(solution_constraints)

                    reified_symbols = reify_program(
                        program_to_reify,
                        calculate_sccs=True,
                    )
                    reified_program = "".join([
                        f"alt({i},{symbol}).\n"
                        for symbol in reified_symbols
                    ])
                    reified_solution_programs.append(reified_program)

        if reified_solution_programs:
            essential_solution_program += "".join(
                reified_solution_programs
            )

        if precompute_solution:
            control = clingo.Control([
                '--project',
                '--warn=none',
                '--parallel-mode=1',
                '--heuristic=Domain',
            ])
            program = self.domain_program
            program += self.solution_program
            program += essential_solution_program
            control.add("base", [], program)
            control.ground([("base", [])])


            control.configuration.solve.models = 1

            if self.solving_timeout:
                with control.solve(
                    async_=True,
                    on_model=lambda model: self.interpret_model(model, verbose),
                ) as handle:
                    finished = handle.wait(self.solving_timeout)
                    if verbose and not finished:
                        print("\nStopped after solving timeout..")
                    else:
                        print()

        program_to_reify = self.domain_program
        program_to_reify += self.puzzle_gen_program
        program_to_reify += self.solution_program
        program_to_reify += essential_solution_program

        program = self.domain_program
        program += self.puzzle_gen_program
        program += self.puzzle_constraints_program
        program += self.solution_program
        program += essential_solution_program

        if precompute_solution:
            program += "\n".join([
                f":- not solution(c({row},{col}),{self.solution[(row, col)]})."
                for row, col in self.solution
            ])

        reified_symbols = reify_program(
            program_to_reify,
            calculate_sccs=True,
        )
        reified_program = "".join([
            f"{symbol}.\n"
            for symbol in reified_symbols
        ])

        glue_program = """
            bot :- true(normal(B)) : output(solution(C,V),B), solution(C,V).
            :- not bot.

            bot :- puzzle(C,V), output(puzzle(C,V),B), fail(normal(B)).
            bot :- not puzzle(C,V), output(puzzle(C,V),B), true(normal(B)).
        """
        if reified_solution_programs:
            glue_program += """
                :- puzzle(C,V),
                    alt(I,output(puzzle(C,V),B)), not alt(I,conjunction(B)).
                :- not puzzle(C,V),
                    alt(I,output(puzzle(C,V),B)), alt(I,conjunction(B)).

                :- guessed_number(Name,Num),
                    alt(I,output(guessed_number(Name,Num),B)),
                    not alt(I,conjunction(B)).
                :- not guessed_number(Name,Num),
                    alt(I,output(guessed_number(Name,Num),B)),
                    alt(I,conjunction(B)).

                :- alt(I), alt(I,conjunction(B)) :
                        alt(I,output(solution(C,V),B)), solution(C,V).
            """

        control = clingo.Control([
            '--project',
            '--warn=none',
            '--parallel-mode=1',
            '--heuristic=Domain',
        ])

        if quality_check_criteria:
            if verbose:
                print("Adding quality check propagator..")
            control.register_propagator(
                QualityCheckPropagator(
                    self.domain_program + \
                    self.solution_program + \
                    "".join(self.essential_solution_constraints),
                    quality_check_criteria,
                )
            )

        control.load("metaD.lp")
        if reified_solution_programs:
            control.load("meta-alt.lp")
        control.add("base", [], program)
        control.add("base", [], reified_program)
        control.add("base", [], glue_program)
        control.ground([("base", [])])
        if verbose:
            print("Done grounding..")


        # Find and yield answer sets
        control.configuration.solve.models = num_models
        control.configuration.solve.opt_mode = "optN"

        if self.solving_timeout:
            with control.solve(
                async_=True,
                on_model=lambda model: self.interpret_model(model, verbose),
            ) as handle:
                finished = handle.wait(self.solving_timeout)
                if verbose and not finished:
                    print("\nStopped after solving timeout..")
                else:
                    print()

        if verbose:
            time = control.statistics['summary']['times']['total']
            print(f"Solving time: {time:.2f} seconds\n")

    def generate_with_cegar(
        self,
        verbose=False,
        num_models=1,
        enforce_essential_constraints=True,
    ):
        """
        TODO
        """

        # TODO: implement precompute_solution
        # TODO: figure out if specific glue option performs better
        #   (i.e., only glue is solution/2 and puzzle/2)

        control = clingo.Control([
            '--project',
            '--warn=none',
            '--parallel-mode=1',
            '--heuristic=Domain',
        ])

        essential_solution_program = ""
        reified_solution_programs = []
        if self.essential_solution_constraints:
            essential_solution_program = "".join(
                self.essential_solution_constraints
            )

            if enforce_essential_constraints:
                for i, solution_constraints in enumerate(list(map(list,
                    combinations(
                        self.essential_solution_constraints,
                        r=len(self.essential_solution_constraints)-1)
                    )
                )):
                    program_to_reify = self.domain_program
                    program_to_reify += self.puzzle_gen_program
                    program_to_reify += self.solution_program
                    program_to_reify += "".join(solution_constraints)

                    reified_symbols = reify_program(
                        program_to_reify,
                        calculate_sccs=True,
                    )
                    reified_program = "".join([
                        f"alt({i},{symbol}).\n"
                        for symbol in reified_symbols
                    ])
                    reified_solution_programs.append(reified_program)

        if reified_solution_programs:
            essential_solution_program += "".join(
                reified_solution_programs
            )

        glue_program = ""
        if reified_solution_programs:
            glue_program += """
                :- puzzle(C,V),
                    alt(I,output(puzzle(C,V),B)), not alt(I,conjunction(B)).
                :- not puzzle(C,V),
                    alt(I,output(puzzle(C,V),B)), alt(I,conjunction(B)).

                :- guessed_number(Name,Num),
                    alt(I,output(guessed_number(Name,Num),B)),
                    not alt(I,conjunction(B)).
                :- not guessed_number(Name,Num),
                    alt(I,output(guessed_number(Name,Num),B)),
                    alt(I,conjunction(B)).

                :- alt(I), alt(I,conjunction(B)) :
                        alt(I,output(solution(C,V),B)), solution(C,V).
            """

        program = self.domain_program
        program += self.puzzle_gen_program
        program += self.puzzle_constraints_program
        program += self.solution_program
        program += essential_solution_program
        program += glue_program

        if reified_solution_programs:
            control.load("meta-alt.lp")
        control.add("base", [], program)
        control.ground([("base", [])])
        if verbose:
            print("Done grounding..")

        # Find and yield answer sets
        control.configuration.solve.models = num_models
        control.configuration.solve.opt_mode = "optN"

        check_program = self.domain_program
        check_program += self.solution_program
        check_program += essential_solution_program

        def symbol_renamer(symbol):
            if symbol == "solution":
                return "other_solution"
            return symbol

        check_ast = []
        parse_string(check_program, lambda ast:
            check_ast.append(rename_symbolic_atoms(ast, symbol_renamer))
        )

        glue_program = """
            solutions_differ :- cell(C), solution(C,V1),
                other_solution(C,V2), V1 != V2.
            :- not solutions_differ.
        """
        parse_string(glue_program,
            check_ast.append
        )

        control.register_propagator(CheckPropagator(check_ast))

        if self.solving_timeout:
            with control.solve(
                async_=True,
                on_model=lambda model: self.interpret_model(model, verbose),
            ) as handle:
                finished = handle.wait(self.solving_timeout)
                if verbose and not finished:
                    print("\nStopped after solving timeout..")
                else:
                    print()

        if verbose:
            time = control.statistics['summary']['times']['total']
            print(f"Solving time: {time:.2f} seconds\n")


class Checker:
    """
    TODO
    """
    _ctl: Control
    _map: List[Tuple[int, int]]

    def __init__(self):
        self._ctl = Control()
        self._map = []

    def backend(self) -> Backend:
        """
        Return the backend of the underlying solver.
        """
        return self._ctl.backend()

    def add(self, guess_lit: int, check_lit: int):
        """
        Map the given solver literal to the corresponding program literal in
        the checker.
        """
        self._map.append((guess_lit, check_lit))

    def ground(self, check_ast):
        """
        Ground the check program.
        """
        # self._ctl.add("base", [], check_program)
        # self._ctl.ground([("base", [])])
        with ProgramBuilder(self._ctl) as bld:
            for stm in check_ast:
                bld.add(stm)
        self._ctl.ground([("base", [])])

    def check(self, control: PropagateControl) -> bool:
        """
        Return true if the check program is unsatisfiable w.r.t. to the atoms
        of the guess program.

        The truth values of the atoms of the guess program are stored in the
        assignment of the given control object.
        """
        assignment = control.assignment

        assumptions = []
        for guess_lit, check_lit in self._map:
            guess_truth = assignment.value(guess_lit)
            assumptions.append(check_lit if guess_truth else -check_lit)

        ret = cast(SolveResult, self._ctl.solve(assumptions))
        if ret.unsatisfiable is not None:
            return ret.unsatisfiable

        raise RuntimeError("search interrupted")


class CheckPropagator(Propagator):
    """
    TODO
    """
    _checkers: List[Checker]
    _gluelits: List[int]

    def __init__(self, check_ast):
        self._checkers = []
        self._check_ast = check_ast
        self._gluelits = []

    def init(self, init: PropagateInit):
        """
        Initialize the solvers for the check programs.
        """
        # we need a checker for each thread (to be able to solve in parallel)
        for _ in range(init.number_of_threads):
            checker = Checker()
            self._checkers.append(checker)

            with checker.backend() as backend:
                for atom in init.symbolic_atoms:

                    if (atom.symbol.name not in ["solution", "puzzle", "guessed_number"]):
                        continue

                    self._gluelits.append(init.solver_literal(atom.literal))

                    guess_lit = init.solver_literal(atom.literal)
                    guess_truth = init.assignment.value(guess_lit)

                    # ignore false atoms
                    if guess_truth is False:
                        continue

                    check_lit = backend.add_atom(atom.symbol)

                    # fix true atoms
                    if guess_truth is True:
                        backend.add_rule([check_lit], [])

                    # add a choice rule for unknow atoms and add them to the
                    # mapping table of the checker
                    else:
                        backend.add_rule([check_lit], [], True)
                        checker.add(guess_lit, check_lit)

            checker.ground(self._check_ast)


    def check(self, control: PropagateControl):
        """
        Check total assignments.
        """
        assignment = control.assignment
        checker = self._checkers[control.thread_id]

        if not checker.check(control):

            conflict = []

            # for level in range(1, assignment.decision_level+1):
            #     conflict.append(-assignment.decision(level))

            for lit in self._gluelits:
                conflict.append(-lit if assignment.is_true(lit) else lit)

            control.add_clause(conflict)


class QualityChecker:
    """
    TODO
    """
    def __init__(self, base_program, quality_check_criteria):
        self._ctl = Control()
        self._map = dict()
        self._base_program = base_program
        self._quality_check_criteria = quality_check_criteria
        if isinstance(quality_check_criteria, str):
            if quality_check_criteria == "lookahead nontrivial":
                self._clingo_args = ["--lookahead=atom"]
                self._choices_threshold = 1
                self._conflicts_threshold = 5
            else:
                raise ValueError('unknown value for quality_check_criteria')
        elif isinstance(quality_check_criteria, list):
            if isinstance(quality_check_criteria[0], str):
                self._clingo_args = [quality_check_criteria[0]]
            else:
                self._clingo_args = quality_check_criteria[0]
            self._choices_threshold = quality_check_criteria[1]
            self._conflicts_threshold = quality_check_criteria[2]

    def backend(self) -> Backend:
        return self._ctl.backend()

    def check(self, control: PropagateControl) -> bool:
        assignment = control.assignment
        puzzle_program = "".join([
            f"{self._map[lit]}.\n"
            for lit in self._map
            if assignment.is_true(lit)
        ])
        clause = [
            -1*lit
            for lit in self._map
            if assignment.is_true(lit)
        ]
        ctl_args = [
            '--project',
            '--warn=none',
            '--parallel-mode=1',
        ]
        ctl_args += self._clingo_args
        new_ctl = clingo.Control(ctl_args)
        new_ctl.add("base", [], self._base_program + puzzle_program)
        new_ctl.ground([("base", [])])
        new_ctl.configuration.solve.models = 1
        new_ctl.solve()
        solver_stats = new_ctl.statistics['solving']['solvers']
        if solver_stats['choices'] < self._choices_threshold or \
            solver_stats['conflicts'] < self._conflicts_threshold:
            print('~', end='')
            return clause
        else:
            return None


class QualityCheckPropagator(Propagator):
    """
    TODO
    """
    _checkers: List[QualityChecker]

    def __init__(self, base_program, quality_check_criteria):
        self._checkers = []
        self._base_program = base_program
        self._quality_check_criteria = quality_check_criteria

    def init(self, init: PropagateInit):
        """
        Initialize the solvers for the check programs.
        """
        # we need a checker for each thread (to be able to solve in parallel)
        for _ in range(init.number_of_threads):
            checker = QualityChecker(
                self._base_program,
                self._quality_check_criteria,
            )
            self._checkers.append(checker)

            with checker.backend() as backend:
                for atom in init.symbolic_atoms:

                    if (atom.symbol.name not in ["puzzle", "guessed_number"]):
                        continue

                    checker._map[init.solver_literal(atom.literal)] = \
                        str(atom.symbol)

    def check(self, control: PropagateControl):
        """
        Check total assignments.
        """
        assignment = control.assignment
        checker = self._checkers[control.thread_id]

        clause = checker.check(control)
        if clause:
            control.add_clause(clause)


enc_library = {
    #
    'three_in_a_row':
    """
    three_in_a_row(c(R,C),c(R,C+1),c(R,C+2)) :-
        cell(c(R,C)), cell(c(R,C+1)), cell(c(R,C+2)).
    three_in_a_row(c(R,C),c(R+1,C),c(R+2,C)) :-
        cell(c(R,C)), cell(c(R+1,C)), cell(c(R+2,C)).
    """,
    #
    'adjacent_cells':
    """
    adjacent_cells(c(R,C),c(R,C+1)) :-
        cell(c(R,C)), cell(c(R,C+1)).
    adjacent_cells(c(R,C),c(R+1,C)) :-
        cell(c(R,C)), cell(c(R+1,C)).
    adjacent_cells(C1,C2) :- adjacent_cells(C2,C1).
    """,
    #
    'ring_around_cell':
    """
    possible_distance(1..board_width).
    possible_distance(1..board_height).
    ring_around_cell(c(R1,C1),c(R2,C2),D) :-
        cell(c(R1,C1)), cell(c(R2,C2)), possible_distance(D),
        |R1-R2| <= D, |C1-C2| <= D.
    """,
    #
    'cell_distance':
    """
    cell_distance(c(R1,C1),c(R2,C2),D) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        D = |R1-R2| + |C1-C2|.
    """,
    #
    'diagonally_adjacent_cells':
    """
    diagonally_adjacent_cells(c(R,C),c(R+1,C+1)) :-
        cell(c(R,C)), cell(c(R+1,C+1)).
    diagonally_adjacent_cells(c(R,C),c(R+1,C-1)) :-
        cell(c(R,C)), cell(c(R+1,C-1)).
    diagonally_adjacent_cells(C1,C2) :- diagonally_adjacent_cells(C2,C1).
    """,
    #
    'knights_move':
    """
    knights_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = 2, |C1-C2| = 1.
    knights_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = 1, |C1-C2| = 2.
    """,
    #
    'pacman_knights_move':
    """
    pknight_dist(1..2).
    pknight_vertical_dist(R1,R2,N) :-
        cell(c(R1,_)), cell(c(R2,_)),
        |R1-R2| = N.
    pknight_vertical_dist(R1,R2,N) :-
        pknight_vertical_dist(R2,R1,N).
    pknight_vertical_dist(R1,R2,N) :-
        cell(c(R1,_)), cell(c(R2,_)),
        pknight_dist(N),
        R1+N > board_height,
        (R1+N) \\ board_height = R2.
    pknight_horizontal_dist(C1,C2,N) :-
        cell(c(_,C1)), cell(c(_,C2)),
        |C1-C2| = N.
    pknight_horizontal_dist(C1,C2,N) :-
        pknight_horizontal_dist(C2,C1,N).
    pknight_horizontal_dist(C1,C2,N) :-
        cell(c(_,C1)), cell(c(_,C2)),
        pknight_dist(N),
        C1+N > board_width,
        (C1+N) \\ board_width = C2.
    pacman_knights_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        pknight_vertical_dist(R1,R2,2),
        pknight_horizontal_dist(C1,C2,1).
    pacman_knights_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        pknight_vertical_dist(R1,R2,1),
        pknight_horizontal_dist(C1,C2,2).
    """,#
    'bishops_move':
    """
    bishops_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = |C1-C2|, C1 < C2, R1 < R2,
        solution(c(R3,C3),e) :
            cell(c(R3,C3)),
            C1 < C3, C3 < C2,
            R1 < R3, R3 < R2,
            |R1-R3| = |C1-C3|.
    bishops_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = |C1-C2|, C1 < C2, R2 < R1,
        solution(c(R3,C3),e) :
            cell(c(R3,C3)),
            C1 < C3, C3 < C2,
            R2 < R3, R3 < R1,
            |R1-R3| = |C1-C3|.
    bishops_move(C1,C2) :- bishops_move(C2,C1).
    """,
    #
    'rooks_move':
    """
    rooks_move(c(R,C1),c(R,C2)) :-
        cell(c(R,C1)), cell(c(R,C2)), C1 < C2,
        solution(c(R,C3),e) :
            cell(c(R,C3)), C1 < C3, C3 < C2.
    rooks_move(c(R1,C),c(R2,C)) :-
        cell(c(R1,C)), cell(c(R2,C)), R1 < R2,
        solution(c(R3,C),e) :
            cell(c(R3,C)), R1 < R3, R3 < R2.
    rooks_move(C1,C2) :- rooks_move(C2,C1).
    """,
    #
    'queens_move':
    """
    bishops_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = |C1-C2|, C1 < C2, R1 < R2,
        solution(c(R3,C3),e) :
            cell(c(R3,C3)),
            C1 < C3, C3 < C2,
            R1 < R3, R3 < R2,
            |R1-R3| = |C1-C3|.
    bishops_move(c(R1,C1),c(R2,C2)) :-
        cell(c(R1,C1)), cell(c(R2,C2)),
        |R1-R2| = |C1-C2|, C1 < C2, R2 < R1,
        solution(c(R3,C3),e) :
            cell(c(R3,C3)),
            C1 < C3, C3 < C2,
            R2 < R3, R3 < R1,
            |R1-R3| = |C1-C3|.
    bishops_move(C1,C2) :- bishops_move(C2,C1).
    rooks_move(c(R,C1),c(R,C2)) :-
        cell(c(R,C1)), cell(c(R,C2)), C1 < C2,
        solution(c(R,C3),e) :
            cell(c(R,C3)), C1 < C3, C3 < C2.
    rooks_move(c(R1,C),c(R2,C)) :-
        cell(c(R1,C)), cell(c(R2,C)), R1 < R2,
        solution(c(R3,C),e) :
            cell(c(R3,C)), R1 < R3, R3 < R2.
    rooks_move(C1,C2) :- rooks_move(C2,C1).
    queens_move(C1,C2) :- bishops_move(C1,C2).
    queens_move(C1,C2) :- rooks_move(C1,C2).
    """
    #
}
