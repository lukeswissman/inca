from itertools import combinations
from itertools import groupby
import clingo
import os
from shutil import copyfile
import re
from random import randint


def limited_subsets_generator(some_set, size):
    """
    Generate all subsets of size "size" from the provided set "some_set" 
    :param some_set: 
    :param size: 
    :return: 
    """
    return list(combinations(some_set, size))


def limited_subsets_pruner(set_to_be_pruned, measurement_element):
    """
    keep elements of "set_to_be_pruned" that contain all elements of "measurements_set" 
    :param set_to_be_pruned: 
    :param measurement_element: 
    :return: 
    """
    return [list(sub_set) for sub_set in set_to_be_pruned if set(measurement_element).issubset(set(sub_set))]


def limited_supersets_pruner(set_to_be_pruned, measurement_element):
    """
    keep elements of "set_to_be_pruned" that do not contain elements of "measurements_set" 
    :param set_to_be_pruned: 
    :param measurement_element: 
    :return: 
    """
    return [list(sub_set) for sub_set in set_to_be_pruned if not set(measurement_element).issubset(set(sub_set))]


def base_set_of_power_set(set_of_sat_sub_sets):
    """
    generate a new set of elements that will be used to calculate larger limited subsets 
    :param set_of_sat_sub_sets: 
    :return: 
    """
    return list(set().union(*set_of_sat_sub_sets))


def super_sets_pruner(some_set_to_prune, sub_sets):
    """
    keep only sets that are not a super set of any set in subsets
    :param some_set_to_prune: 
    :param sub_sets: 
    :return: 
    """
    add = True
    to_keep = []
    for sup_set in some_set_to_prune:
        for sub_set in sub_sets:
            if set(sup_set).issuperset(sub_set):
                add = False
                break
        if add:
            to_keep.append(sup_set)
        add = True
    return to_keep


def super_sets_pruner_advanced(some_set_to_prune, sub_sets, asp_path, problematic):
    """
    from every unsatisfiable super set, keep a subset if this subset is unsatisfiable
    :param some_set_to_prune: 
    :param sub_sets:
    :param asp_path: 
    :return: 
    """
    already_added_a_subset = False
    it_is_a_super_set = False
    to_keep = []
    for super_set in some_set_to_prune:
        for sub_set in sub_sets:

            if set(super_set).issuperset(sub_set):
                it_is_a_super_set = True
                tmp_sup = list(set(super_set).difference(sub_set))
                tmp_sup.append(problematic)
                if check_unsat(tmp_sup, asp_path) != "SAT":
                    if tmp_sup not in to_keep:
                        to_keep.append(tmp_sup)
                        already_added_a_subset = True

        if not already_added_a_subset:
            if not it_is_a_super_set:
                to_keep.append(super_set)

        it_is_a_super_set = False
        already_added_a_subset = False

    return to_keep


def find_minimal_conflict_sets(list_of_options, problematic_option, asp_path):
    """
    find the minimal inconsistent sets of added integrity constraints  
    :param list_of_options: 
    :param problematic_option:
    :param asp_path:
    :return: 
    """
    unlock = True
    set_of_unsat_sub_sets = []
    set_of_sat_sub_sets = []
    size = 2
    list_of_options.append(problematic_option)
    max_size = len(list_of_options)
    full_list_of_options = list(list_of_options)
    sub_sets = limited_subsets_pruner(limited_subsets_generator(list_of_options, size), problematic_option)
    for ss in sub_sets:
        if check_unsat(ss, asp_path) == "SAT":
            set_of_sat_sub_sets.append(ss)
        else:
            set_of_unsat_sub_sets.append(ss)
    while unlock:
        list_of_options = base_set_of_power_set(set_of_sat_sub_sets)
        size += 1
        sub_sets = limited_subsets_pruner(limited_subsets_generator(list_of_options, size), problematic_option)
        sub_sets = super_sets_pruner(sub_sets, set_of_unsat_sub_sets)
        set_of_sat_sub_sets = []
        for ss in sub_sets:
            if check_unsat(ss, asp_path) == "SAT":
                set_of_sat_sub_sets.append(ss)
            else:
                set_of_unsat_sub_sets.append(ss)
        if not list_of_options:
            unlock = False
            print(1)
        if size > max_size:
            unlock = False

    return set_of_unsat_sub_sets


def check_unsat(list_of_options_to_check, asp_path):
    """
    check the unsatisfiability of a list
    :param list_of_options_to_check: 
    :param asp_path:
    :return: 
    """
    # reset the copy
    tmp_asp_path = asp_path[:asp_path.rfind("\\")+1]
    tmp_asp_file = tmp_asp_path + "conflict_tester.txt"
    if os.path.exists(tmp_asp_file):
        os.remove(tmp_asp_file)

    copyfile(tmp_asp_path + "original_asp_program.txt", tmp_asp_file)

    # add new statements
    with open(tmp_asp_file, "a") as tmp:
        for e in add_point(list_of_options_to_check):
            tmp.write(":- " + negate(e) + "\n")
    tmp.close()

    # check whether the asp program is sat or not
    prg = clingo.Control()
    try:
        prg.load(tmp_asp_file)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"

    prg.ground([("base", []), ("parts", [])])
    return str(prg.solve())


def check_unsat_ram(list_of_options_to_check, asp_path):
    """
    check the unsatisfiability of a list
    :param list_of_options_to_check: 
    :param asp_path:
    :return: 
    """

    string_of_constraints = ""

    original_asp_path = asp_path[:asp_path.rfind("\\")+1]
    original_asp_file = original_asp_path + "original_asp_program.txt"

    prg = clingo.Control()
    try:
        prg.load(original_asp_file)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"
    prg.ground([("base", []), ("parts", [])])
    for e in add_point(list_of_options_to_check):
        string_of_constraints += ":- " + negate(e)
    prg.add("", [], string_of_constraints)
    prg.ground([("", [])])
    return str(prg.solve())


def minimal_conflict_set_pruner(minimal_conflict_set, list_of_added_knowledge, problematic_option):
    """
    remove conflict sets that has elements what was not added by the user 
    :param minimal_conflict_set:
    :param list_of_added_knowledge: 
    :param problematic_option:
    :return: 
    """
    pruned_minimal_conflict_set = []
    # problematic_option_list = [problematic_option]
    for mcs in minimal_conflict_set:
        mcs = list(set(mcs).difference(set(problematic_option)))
        if set(mcs).issubset(set(list_of_added_knowledge)):
            pruned_minimal_conflict_set.append(mcs)
    return pruned_minimal_conflict_set


def converter(list_of_lists):
    """
    convert a list of lists to a list
    :param list_of_lists: 
    :return: 
    """
    return [item for sublist in list_of_lists for item in sublist]


def simple_inconsistency_chech(list_of_added_knowledge, problematic_element):
    """
    look for a contradictory pair 
    :param list_of_added_knowledge: 
    :param problematic_element: 
    :return: 
    """
    if negate(problematic_element) in list_of_added_knowledge:
        return True
    else:
        return False


def handle_input_negation(some_list):
    """
    this function handles negated input
    :param some_list: 
    :return: 
    """
    ret = []
    for i in some_list:
        if i[:4] == "#not":
            if i.count("#not") % 2 != 0:
                i = re.sub('#not', '', i).strip()
                i = "not " + i
            else:
                i = re.sub('#not', '', i).strip()
        ret.append(i)
    if len(ret) == 1 and (ret[0] == "not " or ret[0] == ""):
        ret = []
    return ret


def add_point(some_list):
    """
    add a full stop to the end of every predicate
    :param some_list: 
    :return: 
    """
    ret = []
    for i in some_list:
        if len(i) > 0:
            if i[len(i) - 1] != ".":
                i += "."
            ret.append(i)
    return ret


def negate(atom):
    """
    this function will negate the provided atom
    :param atom: 
    :return: 
    """
    if atom[:4] == "not ":
        atom = atom[4:]
    else:
        atom = "not " + atom
    return atom


def two_fronts_check(list_of_added_knowledge,list_of_options, problematic_option, asp_path):
    """
    check small sets, then big sets that are not super sets of unsat small sets,
    and basing on that decide whether to continue or not
    :param list_of_options: 
    :param problematic_option: 
    :param asp_path: 
    :return: 
    """
    not_done = True
    set_of_unsat_sub_sets = []
    set_of_sat_sub_sets = []
    small_size = 2
    original_list_of_options = list(list_of_options)
    list_of_options.append(problematic_option[0])
    max_size = len(list_of_options)
    big_size = max_size - 1
    full_list_of_options = list(list_of_options)
    one_minimal_conflict_set = []

    while not_done:
        sub_sets = limited_subsets_pruner(limited_subsets_generator(list_of_options, small_size), problematic_option)
        for ss in sub_sets:
            if check_unsat(ss, asp_path) == "SAT":
                set_of_sat_sub_sets.append(ss)
            else:
                set_of_unsat_sub_sets.append(ss)
        if set_of_unsat_sub_sets:
            # if [ee for ee in minimal_conflict_set_pruner(set_of_unsat_sub_sets, list_of_added_knowledge, problematic_option) if ee]:
            super_sets = limited_subsets_generator(list_of_options, big_size)
            super_sets = limited_subsets_pruner(super_sets, problematic_option)
            for uss in set_of_unsat_sub_sets:
                super_sets = limited_supersets_pruner(super_sets, uss)
            all_is_sat = True
            if super_sets:
                for sup in super_sets:
                    if check_unsat(sup, asp_path) != "SAT":
                        all_is_sat = False
                        break
            if all_is_sat:
                not_done = False
        else:
            one_minimal_conflict_set = guess_size(original_list_of_options, problematic_option, asp_path)
        if not one_minimal_conflict_set:
            small_size += 1
            big_size -= 1
            list_of_options = base_set_of_power_set(set_of_sat_sub_sets)
        else:
            small_size = len(one_minimal_conflict_set)
            one_minimal_conflict_set = []
    return set_of_unsat_sub_sets


def guess_size(set_of_elements, problematic_element, asp_path):
    """
    guess the initial size of the first potential unsatisfiable subset
    :param set_of_elements: 
    :param problematic_element: 
    :param asp_path: 
    :return: 
    """
    print("That's tricky")
    keep_up = True
    original_list = list(set_of_elements)
    chunk = [problematic_element[0], set_of_elements[0], set_of_elements[len(set_of_elements)-1]]
    print(set_of_elements[0]),
    print(set_of_elements[1])
    print(set_of_elements[len(set_of_elements)-1]),
    print(set_of_elements[len(set_of_elements) - 2])
    set_of_elements = set_of_elements[1:len(set_of_elements)-1]
    print(set_of_elements[0])
    print(set_of_elements[len(set_of_elements) - 1])
    while len(chunk) <= len(original_list)+1:
        if check_unsat(chunk, asp_path) != "SAT":
            while keep_up:
                sub_sets = limited_subsets_generator(chunk, len(chunk)-1)
                sub_sets = [e for e in sub_sets if problematic_element[0] in e]
                unsat_sub_sets = [sub_set for sub_set in sub_sets if check_unsat(sub_set, asp_path) != "SAT"]
                sat_sub_sets = [e for e in sub_sets if e not in unsat_sub_sets]

                if not unsat_sub_sets:
                    return chunk
                if not sub_sets:
                    keep_up = False

                chunk = pruner(sat_sub_sets, unsat_sub_sets, problematic_element[0])
        else:
            new_element_index = randint(0, len(set_of_elements)-1)  # list_of_ind[randint(0, len(list_of_ind)-1)]
            new_element = set_of_elements[new_element_index]
            # list_of_ind = [e for e in list_of_ind if e != new_element_index]
            set_of_elements = [e for e in set_of_elements if set_of_elements.index(e) != new_element_index]
            chunk.append(new_element)


def find_elements_not_in_common(some_list, problamatic_element):
    """
    return elements that are not in the intersection of all sets of somelist
    :param some_list: 
    :return: 
    """
    some_list = [e for e in some_list if problamatic_element in e]
    in_common_elements = set().intersection(*some_list)
    all_elements = set().union(*some_list)
    return list(all_elements.difference(in_common_elements))


def pruner(sat, unsat, problematic):
    """
    keep elements of unsat except one, this one is an element of sat
    :param sat: 
    :param unsat: 
    :return: 
    """
    all_elements = base_set_of_power_set(unsat)
    # sat = [e for e in sat if problematic in e]
    in_common_elements = []
    if sat:
        in_common_elements = list(set(sat[0]).intersection(*sat))
    in_common_elements = [e for e in in_common_elements if problematic != e]
    # candidate = [in_common_elements[randint(0, len(in_common_elements)-1)]]
    # return list(set(all_elements).difference(set(candidate)))
    return list(set(all_elements).difference(set(in_common_elements)))


def pruner_2(unsat):
    """
    keep elements of unsat except one, this one is an element of sat
    :param unsat: 
    :return: 
    """
    unsat = [set(e) for e in unsat]
    return list(set.intersection(*unsat))
    # unsat = [set(e) for e in unsat]
    # sat = [set(e) for e in sat]
    # in_common_unsat = set([])
    # in_common_sat = set([])
    # if unsat:
    #     in_common_unsat = set.intersection(*unsat)
    # if sat:
    #     in_common_sat = set.intersection(*sat)
    # difference = list(in_common_unsat.difference(in_common_sat))
    # difference.append(problematic)
    # return difference


def create_original(original_list_of_options, asp_path):
    """
    create a file that contains the original asp file
    :param original_list_of_options: 
    :param asp_path: 
    :return: 
    """
    # prepare a copy of the current asp program to analyze
    tmp_asp_file = asp_path[:asp_path.rfind(os.sep) + 1] + "original_asp_program.txt"
    if os.path.exists(tmp_asp_file):
        os.remove(tmp_asp_file)

    copyfile(asp_path, tmp_asp_file)

    # rest the copy to the original asp program
    fs = open(tmp_asp_file, "r")
    lines = fs.readlines()
    fs.close()

    fs = open(tmp_asp_file, "w")
    for line in lines:
        found = False
        line = line.strip()
        for inpt in handle_input_negation(original_list_of_options):
            if line == ":- " + negate(inpt):
                found = True
                break
        if not found and line:
            fs.write(line + "\n")
    fs.close()


def do_magic(list_of_added_knowledge, element_in_question, asp_path):
    """"""
    original_list = list(list_of_added_knowledge)
    original_list.append(element_in_question)
    set_of_subsets = limited_subsets_generator(original_list, len(original_list)-1)
    set_of_subsets = [sub_set for sub_set in set_of_subsets if element_in_question in sub_set]
    unsatisfiable_sub_sets = [sub_set for sub_set in set_of_subsets if check_unsat(sub_set, asp_path) != "SAT"]
    satisfiable_sub_sets = [sub_set for sub_set in set_of_subsets if sub_set not in unsatisfiable_sub_sets]
    if satisfiable_sub_sets:
        in_common_elements = list(set(satisfiable_sub_sets[0]).intersection(*satisfiable_sub_sets))
    else:
        in_common_elements = []
    in_common_elements = [e for e in in_common_elements if element_in_question != e]
    minimal_conflict_set = list(set(original_list).difference(set(in_common_elements)))
    return minimal_conflict_set


log = []


def find_minimal_conflict_sets_optimized(set_of_elements, element_in_question, asp_path):
    """"""
    # global for_later, ind
    set_of_unsat_sub_sets = []

    original_list = list(set_of_elements)
    original_list.append(element_in_question)

    small_size = 2
    big_size = len(original_list) - 1

    # for i in range(0, big_size + 1):
    #     log.append([])

    biggest_minus_1 = limited_subsets_generator(original_list, big_size)
    biggest_minus_1 = [sub_set for sub_set in biggest_minus_1 if element_in_question in sub_set]
    biggest_minus_1 = [super_set for super_set in biggest_minus_1 if check_unsat(super_set, asp_path) != "SAT"]

    # for_later = list(biggest_minus_1)
    # ind = len(for_later)-1
    if not biggest_minus_1:
        sub_sets = limited_subsets_generator(original_list, small_size)
        sub_sets = [sub_set for sub_set in sub_sets if element_in_question in sub_set]
        for sub_set in sub_sets:
            if check_unsat(sub_set, asp_path) != "SAT":
                set_of_unsat_sub_sets.append(sub_set)
    # print set_of_unsat_sub_sets

    # in case the original set is the only minimal conflict set
    if not biggest_minus_1:
        if not set_of_unsat_sub_sets:
            return [original_list]
    counter = 0
    # fail_safe = len(biggest_minus_1) + 1
    while biggest_minus_1:
        # fail_safe -= 1
        biggest_minus_1 = super_sets_pruner_advanced(biggest_minus_1, set_of_unsat_sub_sets, asp_path, element_in_question)
        biggest_minus_1.sort(key=len)
        if biggest_minus_1:
            # if fail_safe != 0:
                mcs = deep_dive_advanced(biggest_minus_1[0], element_in_question, asp_path)
                if mcs:
                    counter = 0
                    to_add = True
                    for e in set_of_unsat_sub_sets:
                        possible = set(mcs).intersection(e)
                        if len(possible) > 1:
                            set_of_unsat_sub_sets[set_of_unsat_sub_sets.index(e)] = list(possible)
                            to_add = False
                    if to_add:
                        set_of_unsat_sub_sets.append(list(mcs))
                        # biggest_minus_1 = [e for e in biggest_minus_1 if e != mcs]
                else:
                    biggest_minus_1 = plan_b(biggest_minus_1, set_of_unsat_sub_sets, element_in_question, original_list, counter)
                    counter += 1
                    # fail_safe = len(biggest_minus_1) + 1

    return set_of_unsat_sub_sets


def plan_b(some_set, set_of_unsat_sub_sets, problematic, original,counter):
    """"""
    # global for_later, ind
    to_keep = []
    if len(some_set) > 1:
        if len(some_set[0]) == 3:
            to_keep = limited_subsets_generator(some_set[0], 2)
            to_keep = [e for e in to_keep if problematic in e]
            for i in range(1, len(some_set)):
                to_keep.append(some_set[i])
        else:
            sub_set = set(some_set[0]).intersection(some_set[counter + 1])
            to_keep = list(some_set)
            to_keep[0] = sub_set
            # sub_set = set(some_set[0]).intersection(some_set[1])
            # for i in range(0, len(some_set)):
            #     if not set(some_set[i]).issuperset(sub_set):
            #         to_keep.append(some_set[i])
            # to_keep.append(list(sub_set))
    else:
        new_seed = set(original).difference(converter(set_of_unsat_sub_sets))
        new_seed = list(new_seed.union({problematic}))
        to_keep = limited_subsets_generator(new_seed, len(new_seed) - 1)
        # to_keep = limited_subsets_generator(for_later[ind], len(for_later[ind])-1)#some_set[0], len(some_set[0])-1)
        to_keep = [e for e in to_keep if problematic in e]
        # ind -= 1
    return to_keep


def deep_dive_advanced(set_of_elements, problematic_element, asp_path):
    """"""
    in_common_unsat = []
    sub_sets = limited_subsets_generator(set_of_elements, len(set_of_elements) - 1)
    sub_sets = [list(e) for e in sub_sets if problematic_element in e]
    unsat_sub_sets = [sub_set for sub_set in sub_sets if check_unsat(sub_set, asp_path) != "SAT"]

    if unsat_sub_sets:
        in_common_unsat = pruner_2(unsat_sub_sets)
    else:
        in_common_unsat = set_of_elements
    if len(in_common_unsat) == 1:
        return []
    else:
        return in_common_unsat


def deep_dive(set_of_elements, problematic_element, asp_path):
    """
    guess a minimal conflict set
    :param set_of_elements: 
    :param problematic_element: 
    :param asp_path: 
    :return: 
    """
    global log
    print("That's tricky")
    rand1 = 0
    rand2 = 0
    keep_up = True
    the_same = False
    extended_unsat_sub_sets = []
    original_list = list(set_of_elements)
    # chunk = [problematic_element, set_of_elements[0], set_of_elements[len(set_of_elements) - 1]]
    while not the_same:
        rand1 = randint(0, len(original_list) - 2)
        rand2 = rand1 + 1
        if (set_of_elements[rand1] not in log[1]) and (set_of_elements[rand2] not in log[2]):
            the_same = True
    chunk = [problematic_element, set_of_elements[rand1], set_of_elements[rand2]]
    for i in range(0, 3):
        log[i].append(chunk[i])
    # set_of_elements = set_of_elements[1:len(set_of_elements) - 1]
    set_of_elements = [e for e in set_of_elements if e not in chunk]
    while len(chunk) <= len(original_list) + 1:
        if check_unsat(chunk, asp_path) != "SAT":
        # while keep_up:
            sub_sets = limited_subsets_generator(chunk, len(chunk) - 1)
            sub_sets = [list(e) for e in sub_sets if problematic_element in e]
            unsat_sub_sets = [sub_set for sub_set in sub_sets if check_unsat(sub_set, asp_path) != "SAT"]
            sat_sub_sets = [sub_set for sub_set in sub_sets if sub_set not in unsat_sub_sets]



            extension = set(original_list).difference(chunk)

            all_unsat = True
            xx = []
            yy = []
            for sat_sub_set in sat_sub_sets:
                if check_unsat(list(set(sat_sub_set).union(extension)), asp_path) != "SAT":
                    xx.append(list(set(sat_sub_set).union(extension)))
                    all_unsat = False
                else:
                    yy.append(list(set(sat_sub_set).union(extension)))

            for unsat_sub_set in unsat_sub_sets:
                extended_unsat_sub_set = list(set(unsat_sub_set).union(extension))
                if check_unsat(extended_unsat_sub_set, asp_path) != "SAT":
                    extended_unsat_sub_sets.append(extended_unsat_sub_set)

            candidate = pruner_2(extended_unsat_sub_sets)  # , sat_sub_sets, problematic_element)

            if not all_unsat:
                return candidate
            else:
                set_of_elements = set(chunk).difference(set(candidate))
                set_of_elements = list(set(set_of_elements).union(extension))

                while not the_same:
                    rand1 = randint(0, len(original_list) - 2)
                    rand2 = rand1 + 1
                    if (set_of_elements[rand1] not in log[1]) and (set_of_elements[rand2] not in log[2]):
                        the_same = True
                chunk = [problematic_element, set_of_elements[rand1], set_of_elements[rand2]]
                for i in range(0, 3):
                    log[i].append(chunk[i])
                # set_of_elements = set_of_elements[1:len(set_of_elements) - 1]
                set_of_elements = [e for e in set_of_elements if e not in chunk]
            # if not unsat_sub_sets:
            #     return chunk
            # if not sub_sets:
            #     keep_up = False

        else:
            while the_same:
                new_element_index = randint(0, len(set_of_elements) - 1)  # list_of_ind[randint(0, len(list_of_ind)-1)]
                if set_of_elements[new_element_index] not in log[len(chunk)]:
                    the_same = False
            new_element = set_of_elements[new_element_index]
            chunk.append(new_element)
            log[len(chunk)-1].append(new_element)
            set_of_elements = [e for e in set_of_elements if e != new_element]
            the_same = True


def log_init():
    """
    this function keeps a list of lists of size = len(original_options) where every list corresponds to a random choice
    that was made at the same index as the sub list that contains that choice
    :return: 
    """
    global log
    log = []


def init_group_finder():
    """
    create an asp file, the answer set of this file represents the max groups of rules that go together
    :return: 
    """


def builder(set_of_elements, element_in_question, asp_path, max_size):
    """
    
    :param set_of_elements: 
    :param element_in_question: 
    :param asp_path: 
    :return: 
    """
    could_not_add = []
    to_test = [element_in_question, set_of_elements[0]]
    i = 1
    while i <= len(set_of_elements):
        if check_unsat_ram(to_test, asp_path) != "SAT":
            could_not_add.append(to_test[len(to_test) - 1])
            to_test = to_test[:len(to_test)-1]

        if i < len(set_of_elements):
            to_test.append(set_of_elements[i])
        i += 1
        if len(could_not_add) > max_size:
            i = len(set_of_elements) + 1
    return could_not_add


def build_all(set_of_elements, element_in_question, asp_path):
    counter = 0
    minimal_conflict_sets = []
    already = False
    max_size = len(set_of_elements)
    while counter < len(set_of_elements):
        candidate = builder(set_of_elements, element_in_question, asp_path, max_size)
        for j in range(0, len(minimal_conflict_sets)):
            if set(candidate).issubset(minimal_conflict_sets[j]):
                minimal_conflict_sets[j] = candidate
                if len(candidate) < max_size:
                    max_size = len(candidate)
                already = True
        if not already:
            minimal_conflict_sets.append(candidate)
            if len(candidate) < max_size:
                max_size = len(candidate)
        # minimal_conflict_sets.sort()
        # max_size = len(minimal_conflict_sets[0])
        # minimal_conflict_sets = list(minimal_conflict_sets for minimal_conflict_sets, _ in groupby(minimal_conflict_sets))
        set_of_elements = set_of_elements[1:] + [set_of_elements[0]]
        counter += 1
        already = False
    return [mcs for mcs in minimal_conflict_sets if len(mcs) == max_size]


def build_all_reorder(set_of_elements, element_in_question, asp_path):
    counter = 0
    minimal_conflict_sets = []
    already = False
    original_set_of_elements = list(set_of_elements)
    max_size = len(set_of_elements)
    elements_of_all_mcs = []
    while counter < len(set_of_elements):
        beginning = list(set(set_of_elements).difference(set(elements_of_all_mcs)))
        end = list(set(set_of_elements).difference(beginning))
        end.extend(beginning)
        end.remove(original_set_of_elements[counter])
        set_of_elements = [original_set_of_elements[counter]] + end

        candidate = builder(set_of_elements, element_in_question, asp_path, max_size)
        for j in range(0, len(minimal_conflict_sets)):
            if set(candidate).issubset(minimal_conflict_sets[j]):
                minimal_conflict_sets[j] = candidate
                max_size = len(candidate)
                already = True
        if not already:
            minimal_conflict_sets.append(candidate)
            if len(candidate) < max_size:
                max_size = len(candidate)
        # minimal_conflict_sets.sort()
        # max_size = len(minimal_conflict_sets[0])
        # minimal_conflict_sets = list(minimal_conflict_sets for minimal_conflict_sets, _ in groupby(minimal_conflict_sets))
        elements_of_all_mcs = set().union(*minimal_conflict_sets)
        # set_of_elements = set_of_elements[1:] + [set_of_elements[0]]
        counter += 1
        already = False
    return [mcs for mcs in minimal_conflict_sets if len(mcs) == max_size]
