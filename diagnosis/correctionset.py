import diagnosis
import os


def cs_generator_2(original_list_of_options, problematic, asp_path):
    """
    generate some conflict sets (size 100)
    :param original_list_of_options:
    :param problematic:
    :param asp_path:
    :return:
    """
    global all_minimal_conflict_sets_asp, tmp_asp_path, new_corrections

    all_minimal_conflict_sets_asp = []
    new_corrections = []
    tmp_asp_path = asp_path[:asp_path.rfind(os.sep) + 1]
    tmp_asp_file = tmp_asp_path + "conflict_tester.txt"

    if os.path.exists(tmp_asp_file):
        os.remove(tmp_asp_file)

    Diagnosis.copyfile(tmp_asp_path + "original_asp_program.txt", tmp_asp_file)
    tmp_asp_file = open(tmp_asp_path + "conflict_tester.txt", "a")

    tmp_asp_file.write(":- not remove(_).\n")
    for e in original_list_of_options:
        tmp_asp_file.write("remove(" + str(original_list_of_options.index(e)) + "):- " + Diagnosis.negate(e[:len(e)-1]) + ".\n")
    if len(problematic) > 0:
        if problematic[len(problematic) - 1] != ".":
            problematic += "."
    tmp_asp_file.write(":- " + Diagnosis.negate(problematic) + "\n")
    tmp_asp_file.close()

    return check_unsat_ram_2(tmp_asp_path + "conflict_tester.txt", len(original_list_of_options), original_list_of_options)


def check_unsat_ram_2(asp_path, len_original, original_list_of_options):
    """

    :param asp_path:
    :param len_original:
    :return:
    """

    global new_corrections

    for i in range(1, len_original+1):
        # args = ['--configuration=handy', '-t 4', '--models=0']
        args = ['--models=0', '-t 4']
        prg = Diagnosis.clingo.Control(args)
        try:
            prg.load(asp_path)
        except RuntimeError as rte:
            print(rte)
            return "Parsing Problem"
        prg.ground([("base", []), ("parts", [])])
        tester = ":- not " + str(i) + "#count{X:remove(X)}" + str(i) + "."
        prg.add("", [], tester)
        prg.ground([("", [])])
        # ret = ""
        try:
            ret = str(prg.solve())
        except RuntimeError:
            ret = "UNSAT"
        if ret == "SAT":
            str(prg.solve(on_model=optimal_model_2))
            # break
            tmp_asp_file = open(tmp_asp_path + "conflict_tester.txt", "a")
            for correction_set in index_to_integrity_constraint(new_corrections, original_list_of_options):
                tmp_asp_file.write(correction_set)
            tmp_asp_file.close()
            new_corrections = []

                # prg.add("", [], correction_set)
            # prg.ground([("", [])])
            args = ['--models=1']
            prg = Diagnosis.clingo.Control(args)
            prg.load(asp_path)
            prg.ground([("base", []), ("parts", [])])
            # tester = ":- not #count{X:remove(X)}" + str(i+1) + "."
            # prg.add("", [], tester)
            # prg.ground([("", [])])
            try:
                ret2 = str(prg.solve())
            except RuntimeError:
                ret2 = "UNSAT"
            if ret2 == "SAT":
                print("more to go")
            else:
                print("no more")
                break

    print('Total number of correction sets = ' + str(len(all_minimal_conflict_sets_asp)))
    return all_minimal_conflict_sets_asp


def optimal_model_2(model):
    global all_minimal_conflict_sets_asp, new_corrections
    tmp = []

    for atom in model.symbols(shown=True):
        if "remove(" in str(atom):
            tmp.append(int(str(atom)[str(atom).index("(")+1:str(atom).index(")")]))
    if tmp not in all_minimal_conflict_sets_asp:
        all_minimal_conflict_sets_asp.append(tmp)
        new_corrections.append(tmp)


def index_to_integrity_constraint(correction_sets, original_list_of_options):
    new_integrity_constraints = []
    for l in correction_sets:
        integrity_constraint = ""
        for ind in [i for i in range(0, len(original_list_of_options)) if i in l]:
            integrity_constraint = Diagnosis.negate(original_list_of_options[ind][:len(original_list_of_options[ind])-1]) + "," + integrity_constraint
        new_integrity_constraints.append(":- " + integrity_constraint[0:len(integrity_constraint) - 1] + ".\n")
    return new_integrity_constraints
