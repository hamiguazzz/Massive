import json
import os
import re
from functools import reduce

import numpy as np


class BasisOutputManager:
    type_name = ""
    dimensions = []
    amounts_of_op = {},
    ops_dict = {}

    def __str__(self) -> str:
        return f"basis[type:{self.type_name}, (dim:#op):{str(self.amounts_of_op)}]"

    def __init__(self, filename: str) -> None:
        super().__init__()
        self.__read_json(filename)

    def __read_json(self, filename: str):
        with open(filename, encoding='utf-8') as file_obj:
            data = json.load(file_obj)
            self.type_name = data["type"]
            self.dimensions = data["dimensions"]
            self.ops_dict = {}
            for d in self.dimensions:
                self.ops_dict[d] = data["d" + str(d)]
            self.amounts_of_op = dict(zip(self.dimensions, map(lambda d1: len(self.ops_dict[d1]), self.dimensions)))

    def get_all_len(self):
        d_len_dict = {}
        for d in self.dimensions:
            d_len_dict[d] = list(map(BasisOutputManager.count_equ_length, self.ops_dict[d]))
        return d_len_dict

    @staticmethod
    def count_equ_length(equ: list) -> int:
        total_len = 0
        total_len += 2 * equ.count("\\left(")
        total_len += 1 * equ.count("h")
        total_len += 2 * equ.count("\\operatorname{Tr}")
        total_len += sum(map(BasisOutputManager.__get_indices_counter(), equ))
        return total_len

    @staticmethod
    def __get_indices_counter():
        pattern_ud = re.compile(r"\^\{(.+?)} *_\{(.+?)} *")
        pattern_u = re.compile(r"\^\{(.+?)} *")
        pattern_d = re.compile(r"_\{(.+?)} *")

        # pattern_ud = re.compile(r"^.+?}\^\{(.+?)}_\{(.+?)}$")
        # pattern_u = re.compile(r"^((?<!_).)*\^\{([^_]+?)}((?<!_).)*$")
        # pattern_d = re.compile(r"^((?<!\^).)*_\{([^\^]+?)}((?<!\^).)*$")

        def indices_counter(s: str):
            if s == "h" or s == "\\left(" or s == "\\right)" or s == "\\operatorname{Tr}":
                return 0
            temp = pattern_ud.search(s)
            if temp is None:
                temp = pattern_u.search(s)
                if temp is not None:
                    return 1 + len(temp.group(1).split(" "))
                else:
                    temp = pattern_d.search(s)
                    if temp is not None:
                        return 1 + len(temp.group(1).split(" "))
                    else:
                        # print(f"wrong op:{s}")
                        return 0
            else:
                return 1 + max(len(temp.group(1).split(" ")), len(temp.group(2).split(" ")))

        return indices_counter

    def gen_table(self, d: int, max_column: int,
                  max_length: int = 100, placement: str = "c", add_begin: str = ""):
        empty_equ = "  "

        def prepare_equ(d_parm, column_parm):
            ops = list(zip(self.ops_dict[d_parm], map(BasisOutputManager.count_equ_length, self.ops_dict[d_parm])))
            if len(ops) < column_parm:
                column_parm = len(ops)
            ops.sort(key=lambda t: t[1])
            ops = list(map(lambda t: ("$ \\displaystyle " + " ".join(t[0]) + " $", t[1]), ops))
            # ops += [("  ", 0)] * (column_parm - (len(ops) % column_parm))
            length_dict = dict(ops)
            length_dict[empty_equ] = 0
            ops = np.array(ops)[:, 0]
            ops2 = ops[0: len(ops) - (len(ops) % column_parm)]
            ops2 = np.reshape(ops2, (column_parm, -1))
            ops2 = np.transpose(ops2).tolist()
            if (len(ops) % column_parm) is not 0:
                ops2.append(ops[len(ops) - (len(ops) % column_parm): len(ops)].tolist() + [empty_equ] * (
                        column_parm - (len(ops) % column_parm)))
            ops = ops2
            counted_max_len = max(map(lambda row:
                                      sum(map(lambda equ: length_dict[equ], row)), ops))
            re_tuple = (ops, column_parm)
            if counted_max_len > max_length:
                if column_parm > 1:
                    print(f"too wide! type:{self.type_name} d:{d} len:{counted_max_len}")
                    re_tuple = prepare_equ(d_parm, column_parm - 1)
            return re_tuple

        def gen_form(content_parm, column_parm: int):
            table_env = "longtable"
            spacing = " " * 4
            table_head = "Type: $" + self.type_name + " \\quad \pd=" + str(d) + \
                         " \\quad \\mathcal{O}_{" + str(d) + "}^{" + \
                         ("1" if self.amounts_of_op[d] == 1 else "1\\sim " + str(self.amounts_of_op[d])) + "}$"
            begin_table = f"\\begin{{{table_env}}}[{placement}]{{{'l'.join('|' * (column_parm + 1))}}}\n" \
                          f"{add_begin}{spacing}\\hline\n" \
                          f"{spacing}\\multicolumn{{{column_parm}}}{{|c|}}{{{table_head}}} \\\\ \hline\n" \
                          f"{spacing}\\endfirsthead %\n{spacing}\\endhead%\n" \
                          f"{spacing}\\hline\n{spacing}\\endfoot%\n"
            end_table = f"\n\\end{{{table_env}}}\n\n"

            def gen_row(row_eqs):
                return f"{spacing}{' & '.join(row_eqs)}\\\\ "

            all_lines = list(map(gen_row, content_parm))
            return begin_table + "\\hline\n".join(all_lines) + end_table

        prepared_eqs, column = prepare_equ(d, max_column)
        return gen_form(prepared_eqs, column)

    def gen_section(self, section_head="subsection",
                    has_dimension_section=True, max_column=3, **kwargs):
        if len(self.dimensions) == 0:
            return ""
        section_line = f"\\{section_head}{{Type: ${self.type_name}$ }}\n"
        others = "\n"
        for dim in self.dimensions:
            others += f"\\sub{section_head}{{Dimension = {dim}, " \
                      "$\\mathcal{O}_{" + str(dim) + "}^{" + \
                      ("1" if self.amounts_of_op[dim] == 1 else "1\\sim " + str(self.amounts_of_op[dim])) + "}$ }\n" \
                if has_dimension_section else ""
            others += self.gen_table(dim, max_column, **kwargs)
        return section_line + others


def connect_all_result(path, prefix="result_", filetype="json", **kwargs) -> str:
    files_all = []
    for e in os.walk(path):
        files = filter(lambda s: s.startswith(prefix) and s.endswith('.' + filetype), e[2])
        for f in files:
            files_all.append(e[0] + "\\" + f)
    basis_all = [BasisOutputManager(file) for file in files_all]
    final_result = reduce(lambda rev, ele: f'{rev}\n{ele.gen_section(**kwargs)}', basis_all, "")
    return final_result


if __name__ == '__main__':
    # rt = BasisOutputManager("./4/result_ZZZZ.json")
    # print(rt)
    # print(rt.gen_section())
    # print(rt.gen_section(has_dimension_section=False))
    # print(rt.type_name)
    # print(rt.dimensions)
    # print(rt.ops_dict)
    # print(rt.gen_section())
    with open('result.txt', "w") as writing_file:
        content = connect_all_result(os.path.curdir, has_dimension_section=True, max_column=3, max_length=60)
        writing_file.write(content)
