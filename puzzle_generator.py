"""
TODO
"""

from collections import defaultdict
from itertools import combinations
import textwrap

import clingo
from clingox.reify import reify_program

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
        self.designated_solution_constraints = None

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
    ):
        """
        TODO
        """

        designated_solution_program = ""
        reified_solution_programs = []
        if self.designated_solution_constraints:
            designated_solution_program = "".join(
                self.designated_solution_constraints
            )

            for i, solution_constraints in enumerate(list(map(list,
                combinations(
                    self.designated_solution_constraints,
                    r=len(self.designated_solution_constraints)-1)
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
            designated_solution_program += "".join(
                reified_solution_programs
            )

        if precompute_solution:
            control = clingo.Control([
                '--project',
                '--warn=none',
                '--parallel-mode=4',
                '--heuristic=Domain',
            ])
            program = self.domain_program
            program += self.solution_program
            program += designated_solution_program
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
        program_to_reify += designated_solution_program

        program = self.domain_program
        program += self.puzzle_gen_program
        program += self.puzzle_constraints_program
        program += self.solution_program
        program += designated_solution_program

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

                raar :- alt(I), alt(I,conjunction(B)) :
                        alt(I,output(solution(C,V),B)), solution(C,V).
                #show print(raar) : raar.
            """

        control = clingo.Control([
            '--project',
            '--warn=none',
            '--parallel-mode=4',
            '--heuristic=Domain',
        ])
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
