import clingo
from diagnosis import diagnosis
from diagnosis import correctionset
import operator
import time
import re
from itertools import chain, combinations
import os
from shutil import copyfile
import datetime
from argparse import ArgumentParser

asp_file_name = os.getcwd() + os.sep + "asp.txt"

logs = []
union_of_answers_without_c = []
list_of_indices = []
list_of_difference_blue = []
list_of_difference_red = []
list_of_difference_white = []
tmp_prev_red = []
tmp_prev_blue = []
tmp_prev_white = []
list_of_answer_sets = []
list_of_predicates_not_to_negate = []
list_of_predicates = []
list_of_added_knowledge = []
first_ever = []
first_answer_set_ever = []
last_answer_set = []
allowed_entries = {}
init_first_answer_set = True
conf_pr = True
was_sat = ""
consequences = []
what_if_white = []


minimal_conflict_sets_asp = []


class UnsatObject:
    """ 
    this class represents an object that contains facts and the rules that they violate
    """
    def __init__(self, facts, rules):
        """ 
        initialise an element of type UsatObject
        :param facts:
        :param rules: 
        """
        self.facts = facts
        self.rules = rules


class PredicateIndex:
    """ 
    name of the predicate plus an index to indicate which list corresponds to that predicate in the model (the model is list of lists)
    """
    def __init__(self, predicate_name, ind):
        """ 
        initialise an element of type PredicateIndex
        :param predicate_name: 
        :param ind: 
        """
        self.p_name = predicate_name
        self.p_index = ind 


class Predicate:
    """ 
    predicate and its arguments
    """
    def __init__(self, predicate_name):
        """ 
        Initialise an element of type Predicate
        :param predicate_name: 
        """
        self.p_name = predicate_name
        self.p_elements = []

    @staticmethod
    def add_elements(predicate, predicate_element):
        """ 
        fill the elements associated to the predicate
        :param predicate: 
        :param predicate_element: 
        :return: 
        """
        # tmp = []
        # for e in predicate_element:
        #     try:
        #         tmp.append(int(str(e)))
        #     except ValueError:
        #         tmp.append(str(e))
        # if not (tmp in predicate.p_elements):
        #     predicate.p_elements.append(tmp)

        x = ""
        for part in predicate_element:
            x = x + str(part) + ',' 
        x = x[:-1]
        predicate_element = x 
        if not (predicate_element in predicate.p_elements):
            predicate.p_elements.append(predicate_element)


def print_why_hitting(to_keep):
    """
    print the reasons in a form of possible deletions
    :param reasons: 
    :return: 
    """
    global input_list
    reasons = []
    start = '\033[95m'
    under_line = '\033[4m'
    end = '\033[0m'
    first = "To be able to select "
    for e in input_list:
        first += e[:len(e)-1] + ", "
    first = first[:len(first)-2] + " you have to remove "
    for l in to_keep:
        tmp = []
        for ind in [i for i in range(0, len(list_of_added_knowledge)) if i in l]:
            tmp.append(list_of_added_knowledge[ind])
        reasons.append(tmp)
    second = ""
    intersection = diagnosis.pruner_2(reasons)
    if len(intersection) != len(reasons[0]):
        for i in intersection:
            second += start + i[:len(i)-1] + end + " " + under_line + "and" + end + " "
        if len(reasons) > 2:
            second += "one of the following combinations\n\t"
        else:
            second += "\n\t"
        for reason in reasons:
            for r in list(set(reason).difference(set(intersection))):
                second += start + r[:len(r)-1] + end + ", "
            second = second[:len(second) - 2]
            second += "\n" + under_line + "or" + end + "\n\t"
        second = second[:second.rfind("\n", 0, second.rfind("\n")) + 1]
    else:
        if len(reasons) > 2:
            first += " one of the following combinations\n\t"
        else:
            first += "\n\t"
        for reason in reasons:
            for r in reason:
                second += start + r[:len(r) - 1] + end + ", "
            second = second[:len(second) - 2]
            second += "\n" + under_line + "or" + end + "\n\t"
        second = second[:second.rfind("\n", 0, second.rfind("\n")) + 1]

    print(first + second)


def model_consequences(model):
    """
    :param model: 
    :return: 
    """
    assert isinstance(model, clingo.Model)
    global consequences
    consequences = []
    for atom in model.symbols(atoms=True):
        if atom.negative:
            tmp = "-"
        else:
            tmp = ""
        for argument in [atom.arguments]:
            x = ""
            for part in argument:
                x = x + str(part) + ','
            x = x[:-1]
            consequences.append(tmp + atom.name + "(" + x + ")")
    return consequences


def get_consequences(fourth, list_of_atoms_to_delete_before_start):
    """
    get the consequence atoms of adding certain atoms
    :param: fourth
    :param: list_of_atoms_to_delete_before_start
    :return: 
    """
    global consequences, list_of_predicates_not_to_negate
    atoms_to_consider = fourth  #fourth.split(", ")
    new_asp_file = asp_file_name[:asp_file_name.rfind("\\") + 1] + "tmp\\tmp\\" + asp_file_name[asp_file_name.rfind("\\") + 1:]
    copyfile(asp_file_name, new_asp_file)
    fs = open(new_asp_file, "r")
    lines = fs.readlines()
    fs.close()
    fs = open(new_asp_file, "w")
    for line in lines:
        found = False
        line = line.strip()
        for inpt in handle_input_negation(atoms_to_consider):#list_of_atoms_to_delete_before_start):  #  #list_of_added_knowledge):
            if line == inpt:
                found = True
                break
        if not found and line:
            fs.write(line + "\n")
    # for e in add_point(atoms_to_consider):
    #     fs.write(e + "\n")
    # fs.close()
    prg = clingo.Control(['--enum-mode=cautious'])
    try:
        prg.load(new_asp_file)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"

    prg.ground([("base", []), ("parts", [])])
    prg.solve(on_model=model_consequences)
    white = []
    for lst in list_of_difference_white:
        white = set(white).union(lst)
    # consequences = (set(consequences).intersection(white)).difference(set(atoms_to_consider))
    consequences = (set(white).difference(consequences)).difference(set(atoms_to_consider))
    # consequences = set(add_point(set(consequences).difference(set(first_ever)))).difference(set(atoms_to_consider))
    return consequences


def check_unsatisfiability_facts(asp_file):
    """
    go throw all programs in tmp\tmp\ and see which ones are unsatisfied
    :param asp_file: 
    :return: 
    """
    # all_unsat = True
    list_of_unsat_objects = []
    # path = asp_file[:asp_file.rfind("\\")] + "\\tmp\\tmp"
    # for tmp_file in [f for f in os.listdir(path) if f.endswith('.txt')]:
    #     tmp_file = path + "\\" + tmp_file
    facts = []
    rules = []
    prg = clingo.Control()
    try:
        prg.load(asp_file)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"

    prg.ground([("base", []), ("parts", [])])
    ret = prg.solve()
        # if str(ret) != "SAT":
        #     fs = open(tmp_file, "r")
        #     lines = fs.readlines()
        #     fs.close()
        #     only_rules = False
        #     for line in lines:
        #         if "%%%% end of facts to test %%%%" in line:
        #             only_rules = True
        #         elif ":-" in line:
        #             rules.append(line)
        #         elif "%" != line[0] and not only_rules:
        #             facts.append(line)
        #         # if not rules_turn:
        #         #     if "%%%% end of facts to test %%%%" not in line:
        #         #         if ":-" not in line:
        #         #             facts.append(line)
        #         #     else:
        #         #         rules_turn = True
        #         #         unsatobject = UnsatObject(facts)
        #         # else:
        #         #     if ":-" in line:
        #         #         unsatobject.add_rules()
        #
        #     list_of_unsat_objects.append(UnsatObject(rules=rules, facts=facts))
        # else:
        #     all_unsat = False

    for unsatobject in list_of_unsat_objects:
        length_in_question = len(unsatobject.facts)
        for object_with_larger_list in [e for e in list_of_unsat_objects if len(e.facts) > length_in_question]:
            if set(unsatobject.facts).issubset(object_with_larger_list.facts):
                del list_of_unsat_objects[list_of_unsat_objects.index(object_with_larger_list)]

    # if all_unsat:
    #     for e in list_of_unsat_objects:
    #         e.facts = []
    return list_of_unsat_objects


def some_callback_fun(ast):
    """
    :return: 
    """
    if ast.type == clingo.ast.ASTType.Rule and ast.body:
        print (ast.head)


def show_bad_input(input_list_after, input_list_before):
    """
    display ignored atoms
    :param input_list_after: 
    :param input_list_before: 
    :return: 
    """
    global list_of_difference_white
    already_added = []
    tmp_dif = set(input_list_before).difference(set(input_list_after))
    for e in tmp_dif:
        if "(" in e:
            ind = [x.p_index for x in list_of_indices if x.p_name == e[:e.index("(")]]
            if len(ind) > 0:
                if e in add_point(list_of_difference_white[ind[0]]):
                    already_added.append(e)
    tmp_dif = set(tmp_dif).difference(already_added)
    if len(already_added) == 1:
        print("\nThe following element was already chosen\n")
    elif len(already_added) > 1:
        print("\nThe following elements were already chosen\n")
    for e in already_added:
        print(str(e) + "\n")
    if len(tmp_dif) == 1 and tmp_dif:
        print("\nThe following element is not a valid option\n")
    elif len(tmp_dif) > 1:
        print("\nThe following elements are not valid options\n")
    for e in tmp_dif:
        print(str(e) + "\n")


def print_options(some_list, color='\033[0m'):
    """
    a function that prints the elements of a list
    :param some_list: 
    :param color: is a string that represents the color of the printed elements
    :return: 
    """
    if some_list:
        if len(max(some_list, key=len)) >= 16:
            lim = 6
        else:
            lim = 8
        c = 0
        for element in some_list:
            if c == lim:
                c = 0
                print("\n")
            c += 1
            print(color + element + '\033[0m' + " "),
        print("\n")


def initial_display(clingo_return):
    """
    this function is responsible of displaying the initial options for the user
    :param clingo_return: 
    :return: 
    """
    if clingo_return == "SAT":
        global conf_pr, allowed_entries
        to_print = []
        if not list_of_added_knowledge:
            for element in list_of_answer_sets[len(list_of_answer_sets) - 1]:
                for arguments in element.p_elements:
                    predicate = element.p_name + "(" + arguments + ")."
                    if predicate not in first_ever:
                        to_print.append(predicate)
            if to_print:
                allowed_entries = set(to_print)
                print('\033[1;33m' + "\nThe following options are available:\n" + '\033[0m')
                print_options(to_print)
            else:
                print('\033[1;33m' + "\nThe provided problem has nothing to be configured!\n" + '\033[0m')
                conf_pr = False


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


def add_break_line(some_list, is_string=False):
    """
    add a \n to the end of every element in some list in case is_string false, is_string should be set to true if some list is a string 
    :param some_list: 
    :param is_string:
    :return: 
    """
    ret = []
    if not is_string:
        for i in some_list:
            if not i.endswith("\n") and len(i.strip()) > 0:
                i += "\n"
            ret.append(i)
        return ret
    else:
        if not some_list.endswith("\n") and len(some_list.strip()) > 0:
            some_list += "\n"
        return some_list


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


def change_dash_to_not(predicate):
    """
    
    :param predicate: 
    :return: 
    """
    if predicate[0] == "-":
        predicate.replace("-", "not_")
    return predicate


def translator_not(asp_file):
    """
    determine which predicates should not be negated
    :param asp_file:
    :return:
    """
    global list_of_predicates_not_to_negate, first_ever
    list_of_predicates_not_to_negate = []
    args = ['--enum-mode=cautious']
    prg = clingo.Control(args)
    try:
        prg.load(asp_file)
    except RuntimeError:
        return None
    prg.ground([("base", []), ("parts", [])])
    ret = prg.solve(on_model=model_function_not)
    # i = 0
    # for model in list_of_predicates_not_to_negate:
    #     print('\033[1;33m' + "\nAnswer Set %i" % (i+1) + '\033[0m')
    #     for predicate in model:
    #         print("\n" + "instances of " + predicate.p_name + ":\n")
    #         for argument in predicate.p_elements:
    #             x = ""
    #             for part in argument:
    #                 x = x + str(part) + ','
    #             x = x[:-1]
    #             print (predicate.p_name + "(" + x + ")")
    #     i += 1
    if str(ret) == "SAT":
        if init_first_answer_set:
            first_ever = list_of_predicates_not_to_negate


def translator(asp_file, deep_investigation):
    """
    take an ASP file and extract info from it
    :param asp_file:
    :param deep_investigation:
    :return:
    """
    global list_of_answer_sets, first_answer_set_ever, init_first_answer_set

    # '--enum-mode=cautious' '--models=0'

    translator_not(asp_file)
    list_of_answer_sets = []
    args = ['--enum-mode=brave']
    prg = clingo.Control(args)
    # print(prg.configuration)
    try:
        prg.load(asp_file)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"

    prg.ground([("base", []), ("parts", [])])
    ret = prg.solve(on_model=create_last_answer_set)
    if str(ret) == "SAT":
        model_function(last_answer_set[len(last_answer_set) - 1])
        if init_first_answer_set:
            first_answer_set_ever = list_of_answer_sets[len(list_of_answer_sets) - 1]

        if len(first_answer_set_ever) != 0 and len(list_of_answer_sets) != 0 and not init_first_answer_set:
            if len(list_of_answer_sets[0]) != 0:
                compare(first_answer_set_ever, list_of_answer_sets[len(list_of_answer_sets) - 1], deep_investigation)

        init_first_answer_set = False
    initial_display(str(ret))
    return str(ret)


def create_last_answer_set(model):
    """
    just find the last Answer set
    :param model: 
    :return: 
    """
    assert isinstance(model, clingo.Model)
    global last_answer_set
    last_answer_set = [model.symbols(atoms=True)]


def model_what_if(model):
    """

    :param model: 
    :return: 
    """
    assert isinstance(model, clingo.Model)
    global what_if_white
    what_if_white = []
    for atom in model.symbols(atoms=True):
        if atom.negative:
            tmp = "-"
        else:
            tmp = ""
        for argument in [atom.arguments]:
            x = ""
            for part in argument:
                x = x + str(part) + ','
            x = x[:-1]
            what_if_white.append(tmp + atom.name + "(" + x + ")")


def model_function_not(model):
    """

    :param model: 
    :return: 
    """
    assert isinstance(model, clingo.Model)
    global list_of_predicates, list_of_predicates_not_to_negate
    list_of_predicates_not_to_negate = []
    for atom in model.symbols(atoms=True):
        if atom.negative:
            tmp = "-"
        else:
            tmp = ""
        for argument in [atom.arguments]:
            x = ""
            for part in argument:
                x = x + str(part) + ','
            x = x[:-1]
            list_of_predicates_not_to_negate.append(tmp + atom.name + "(" + x + ")")


def model_function(model):
    """
    
    :param model: 
    :return: 
    """
    # assert isinstance(model, clingo.Model)
    found = False
    global list_of_predicates, list_of_predicates_not_to_negate
    list_of_predicates = []
    for atom in model: # model.symbols(atoms=True):
        if atom.negative:
            tmp = "-"
        else:
            tmp = ""
        if not list_of_predicates:

            predicate = Predicate(tmp + atom.name)
            Predicate.add_elements(predicate, atom.arguments)

            # for argument in [predicate.p_elements[len(predicate.p_elements) - 1]]:
            #     x = ""
            #     for part in argument:
            #         x = x + str(part) + ','
            #     x = x[:-1]

            if predicate.p_name + "(" + predicate.p_elements[len(predicate.p_elements) - 1] + ")" not in first_ever:

                list_of_predicates.append(predicate)

                predicate = Predicate(negate(tmp + atom.name))
                Predicate.add_elements(predicate, atom.arguments)

                list_of_predicates.append(predicate)
        else:
            for i in range(len(list_of_predicates)):
                if list_of_predicates[i].p_name == atom.name:
                    predicate = list_of_predicates[i]
                    Predicate.add_elements(predicate, atom.arguments)
                    # for argument in [predicate.p_elements[len(predicate.p_elements) - 1]]:
                    #     x = ""
                    #     for part in argument:
                    #         x = x + str(part) + ','
                    #     x = x[:-1]
                    if predicate.p_name + "(" + predicate.p_elements[len(predicate.p_elements) - 1] + ")" not in first_ever:
                        name_in_list = [x for x in list_of_predicates if x.p_name == negate(atom.name)]
                        if len(name_in_list) > 0:
                            predicate = name_in_list[0]
                        else:
                            predicate = Predicate(negate(tmp + atom.name))
                            list_of_predicates.append(predicate)
                        Predicate.add_elements(predicate, atom.arguments)
                    found = True
                    break

            if not found:
                predicate = Predicate(tmp + atom.name)
                Predicate.add_elements(predicate, atom.arguments)

                # for argument in [predicate.p_elements[len(predicate.p_elements) - 1]]:
                    # x = ""
                    # for part in argument:
                    #     x = x + str(part) + ','
                    # x = x[:-1]
                if predicate.p_name + "(" + predicate.p_elements[len(predicate.p_elements) - 1] + ")" not in first_ever:

                    list_of_predicates.append(predicate)

                    predicate = Predicate(negate(tmp + atom.name))
                    Predicate.add_elements(predicate, atom.arguments)

                    list_of_predicates.append(predicate)
            found = False
    list_of_answer_sets.append(list_of_predicates)
    return None


def compare(old_model, new_model, deep_investigation):
    """
    This method compares the last new generated model with the last previous model and detects the missing predicates or
    the ones added newly
    :param old_model: 
    :param new_model: 
    :param deep_investigation:
    :return: 
    """
    global tmp_prev_red, tmp_prev_blue, list_of_difference_red, list_of_difference_blue, list_of_indices, list_of_difference_white, input_list,\
        asp_file_name, union_of_answers_without_c, tmp_prev_white

    if len(old_model) > len(new_model):
        for e in old_model:
            if e.p_name not in [n.p_name for n in new_model]:
                new_model.append(Predicate(e.p_name))

    old_model.sort(key=operator.attrgetter('p_name'))
    new_model.sort(key=operator.attrgetter('p_name'))
    if first_run:
        for i in range(len(old_model)):
            list_of_indices.append(PredicateIndex(old_model[i].p_name, i))

    for i in range(len(old_model)):
        list_of_difference_blue[i] = []
        list_of_difference_red[i] = []
        list_of_difference_white[i] = []
        tmp_prev_red[i] = []

    if list_of_added_knowledge:

        for i in range(len(old_model)):

            if old_model[i].p_name == new_model[i].p_name and old_model[i].p_name[:4] != "not ":

                old_model[i].p_elements.sort()
                new_model[i].p_elements.sort()

                for e in [old_model[i].p_name + "(" + str(j) + ")" for j in old_model[i].p_elements if j not in new_model[i].p_elements]:
                    list_of_difference_red[i].append(e)
                for e in [old_model[i].p_name + "(" + str(j) + ")" for j in old_model[i].p_elements if
                          j not in [m for m in old_model[i].p_elements if m not in new_model[i].p_elements]]:
                    list_of_difference_blue[i].append(e)
                list_of_difference_white[i] = list(set(list_of_predicates_not_to_negate).intersection(list_of_difference_blue[i]))
                list_of_difference_blue[i] = list(set(list_of_difference_blue[i]).difference(set(list_of_difference_white[i])))

                list_of_difference_red[i] = [e for e in list_of_difference_red[i] if (e not in list_of_difference_blue[i] and e in tmp_prev_red[i]) or
                                          (e not in tmp_prev_red[i])]

                tmp_prev_red[i] = [e for e in list_of_difference_red[i] if e not in tmp_prev_red[i]]

        # predicate names that start with a letter greater than n

        for i in range(len(old_model)):

            if old_model[i].p_name == new_model[i].p_name and old_model[i].p_name[:4] == "not ":
                ind = [x.p_index for x in list_of_indices if x.p_name == old_model[i].p_name[4:]][0]
                tmp = []
                for e in range(len(list_of_difference_blue[ind])):
                    tmp.append(negate(list_of_difference_blue[ind][e]))
                for e in tmp:
                    list_of_difference_blue[i].append(e)

                tmp_blue = []
                p_name = negate(new_model[i].p_name)
                ind = [x for x in list_of_indices if x.p_name == p_name][0].p_index

                for argument in new_model[ind].p_elements:
                    # x = ""
                    # for part in argument:
                    #     x = x + str(part) + ','
                    # x = x[:-1]
                    tmp_blue.append(new_model[ind].p_name + "(" + argument + ")")

                for_sure_blue = list_of_difference_white[ind]
                # for_sure_blue = list(set(tmp_blue).intersection(list_of_predicates_not_to_negate))

                for element in for_sure_blue:

                    predicate_name = element[:element.index("(")]
                    predicate_name = negate(predicate_name)

                    #predicate_elements = []
                    x = ""
                    for e in element[element.find("(") + 1:element.rfind(")")].split(","):
                        #try:
                        #    predicate_elements.append(int(x))
                        x = x + str(e) + ','
                    x = x[:-1]
                        #except ValueError:
                        #    predicate_elements.append(str(x))

                    #predicate = predicate_name + str(predicate_elements)
                    predicate = predicate_name + "(" + x + ")"

                    list_of_difference_red[i].append(predicate)

        # if input_list:
        #     intermediate_check(asp_file_name, input_list)
        #     if union_of_answers_without_c:
        #         modify_red_blue()

        # print_red_blue_white()

        # l njme 3'alat
        if deep_investigation:
            start = '\033[95m'
            end = '\033[0m'
            flat_list_white = diagnosis.converter(list_of_difference_white)
            flat_prev_white = add_point(diagnosis.converter(tmp_prev_white))
            if set(add_point(flat_list_white)).difference(set(list_of_added_knowledge)).difference(set(flat_prev_white)):
                first = "The selection of "
                for element in input_list:
                    first += start + element[:len(element)-1] + end + ", "
                first = first[:len(first)-2]
                second = " also requires the selection of "
                for element in list(set(add_point(flat_list_white)).difference(set(list_of_added_knowledge))):
                    if element not in add_point(flat_prev_white):
                        second += start + element[:len(element)-1] + end + ", "
                second = second[:len(second)-2]
                display_text = first + second + "\ndo you want to continue?(y/n)\n"
                option = raw_input(display_text)
                if option.lower() == 'y':
                    print_red_blue_white()
                else:
                    del_function(asp_file_name, input_list, False)
                    input_list = []
                    translator(asp_file_name, True)
                print("-----------------------------\n")
            else:
                print_red_blue_white()
        tmp_prev_white = list(list_of_difference_white)


def print_red_blue_white():
    """
    
    :return: 
    """
    one = True
    two = True
    three = True
    print("-----------------------------\n")
    if len(set(tuple(i) for i in list_of_difference_red).intersection(set(tuple(i) for i in list_of_difference_red))) > 1:
        print_options(["Unavailable Options:"], '\033[1;33m')
        for lst in list_of_difference_red:
            print_options(lst, '\033[1;31m')
    else:
        one = False
    if one:
        if len(set(tuple(i) for i in list_of_difference_blue).intersection(set(tuple(i) for i in list_of_difference_blue))) > 1:
            print_options(["Available Options:"], '\033[1;33m')
            for lst in list_of_difference_blue:
                print_options(lst, '\033[1;34m')
        else:
            two = False

        if len(set(tuple(i) for i in list_of_difference_white).intersection(set(tuple(i) for i in list_of_difference_white))) > 1:
            print_options(["Final Configuration:"], '\033[1;33m')
            for lst in list_of_difference_white:
                print_options(lst)
        else:
            three = False
    if not one:  # and not two and not three and list_of_added_knowledge:
        translator(asp_file_name, True)


def was_unsat_inspection():

    print('\033[1;31m' + "\nThe provided asp-program might be UNSAT or there are syntax errors, please check it and run the program again!" + '\033[0m')


def was_sat_inspection(asp_file_name, input_list):
    """
    This function is responsible of finding what caused the unsatisfiability in case the asp-program was satisfiable at the beginning of the program 
    :return: 
    """
    global list_of_difference_red, list_of_indices
    red_elements = []
    blue_elements = []
    already_considered = []
    problematic = []
    size = 0
    for x in [len(e) for e in list_of_difference_red]:
        size += x

    if list_of_indices and size > 0:

        for element in list_of_added_knowledge:
            predicate_name = element[:element.index("(")]
            #predicate_elements = element[element.find("(")+1:element.rfind(")")]
            #predicate = predicate_name + "[" + predicate_elements + "]"
            predicate = element[:len(element)-1]

            red_index = 0
            for x in list_of_indices:
                if x.p_name == predicate_name:
                    red_index = x.p_index
                    break

            tmp = "".join(str(predicate).split())
            for x in list_of_difference_red[red_index]:
                if ("".join(x.split())).replace("\'", "") == tmp:
                    red_elements.append(predicate)
                    break
            for x in list_of_difference_blue[red_index]:
                if ("".join(x.split())).replace("\'", "") == tmp:
                    blue_elements.append(predicate)
                    break

        to_delete = []
        if len(red_elements) > 0:
            print("\nElements displayed in red can't be chosen\n")
            for x in red_elements:
                print(x)
                to_delete.append(x + ".")
        if len(blue_elements) > 0:
            for x in blue_elements:
                if negate(x) in blue_elements:
                    if x not in already_considered and negate(x) not in already_considered:
                        already_considered.append(x)
                    to_delete.append(x + ".")
            if already_considered:
                print("\nThe following element(s) can't be chosen because \n")
                for x in already_considered:
                    print(x + " contradicts " + negate(x))
            rest = [e for e in blue_elements if e not in already_considered and negate(e) not in already_considered]
            del_function(asp_file_name, to_delete, False)
            to_delete = []
            if len(rest) > 0:
                prg = clingo.Control()
                try:
                    prg.load(asp_file_name)
                except RuntimeError as rte:
                    print(rte)
                    return "Parsing Problem"

                prg.ground([("base", []), ("parts", [])])
                ret = prg.solve()
                if str(ret) != "SAT":
                    print("\nThe following element(s) can't be chosen because \n")
                    if len(rest) == 1:
                        print("\nThe following atom\n")
                    else:
                        print("\nThe combination of the following atoms\n")
                    for x in rest:
                        print(x + " "),
                        problematic.append(x)
                        to_delete.append(x + ".")
                    print("\n\nviolates a rule or more in the program\n")
                else:
                    if len(rest) == 1:
                        print("\nThe following atom has been added\n")
                    else:
                        print("\nThe following atoms have been added\n")
                    for x in rest:
                        print(x + " ")
        print("")
        del_function(asp_file_name, to_delete, False)
        if problematic:
            suggest_options(problematic, asp_file_name)
        translator(asp_file_name, True)

    else:

        list_of_indices = []
        print ("\nInconsistent Entries\nWhat you have just entered caused the program to be UNSAT\nDeleting all new entries")
        time.sleep(2)
        del_function(asp_file_name, list_of_added_knowledge)
        for i in range(len(first_answer_set_ever)):
            list_of_indices.append(PredicateIndex(first_answer_set_ever[i].p_name, i))

    return red_elements


def suggest_options(problematic, asp_file_name):
    max_size_option = len(problematic) - 1
    list_of_possibilities = list(chain.from_iterable(combinations(problematic, r) for r in range(len(problematic)+1)))
    list_of_sat_possibilities = []
    for possibility in list_of_possibilities:
        for element in possibility:
            try:
                asp_file = open(asp_file_name, "a")
                asp_file.write("\n" + ":- " + negate(add_point([element])[0]))
                asp_file.close()
            except IOError:
                print("Error! Can not access " + asp_file_name)
                asp_file.close()
        if len(possibility) > 0:
            prg = clingo.Control()
            try:
                prg.load(asp_file_name)
            except RuntimeError as rte:
                print(rte)
                return "Parsing Problem"

            prg.ground([("base", []), ("parts", [])])
            ret = prg.solve()
            if str(ret) == "SAT":
                list_of_sat_possibilities.append(list(possibility))
            del_function(asp_file_name, add_point(possibility), False)

    if len(list_of_sat_possibilities) > 0:
        print("But you can choose one of the following combinations\n")
        for i in range(len(list_of_sat_possibilities)):
            print(str(i+1) + ")\t"),
            print_options(list_of_sat_possibilities[i], '\033[94m')
        print("-----------------------------\n")


def handle_input(asp_file_name):
    """
    this function is the interactive part with the user
    here you can skip with empty string ""
    add predicates
    remove any line from tha asp file
    :param asp_file_name:
    :return:
    """
    global list_of_added_knowledge, first_run, list_of_predicates_names, input_list, logs
    display_text = '\033[1;33m' + "Here you can apply your choices by adding atoms (ex: xx(y1,y2) / #not xx(y1,y3)) or\ntype \"#del\" " \
                                "plus the atoms you want to delete separated by \"/\" or\n\"delall\" to delete all the added atoms.\n" \
                   + '\033[0m'
    display_text2 = '\033[1;33m' + "Type help to list commands\n" + '\033[0m'
    input_text = ""
    if first_run:
        init_predicates_names()
    while input_text.lower() != "exit":

        input_text = raw_input(display_text2)
        input_text = "".join(input_text.split())
        if "exit" not in input_text.lower():
            os.system('cls' if os.name == 'nt' else 'clear')
            if input_text != "" and "#del" != input_text[:4].lower() and "delall" != input_text.lower() and "lk" != input_text.lower() \
                    and "#how" != input_text[:4].lower() and "help" != input_text[:4].lower() and "show" != input_text[:4].lower() and "#what" != \
                    input_text[:5].lower():

                input_list = input_text.split("/")
                input_list = handle_input_negation(input_list)
                if input_list:
                    tmp = [e for e in input_list if e]
                    tmp = add_point(tmp)

                    # input_list = [e for e in tmp if e.split("(")[0] in list_of_predicates_names]
                    # update_configurables()

                    input_list = [e for e in tmp if e in update_configurables()]  # allowed_entries]
                    show_bad_input(input_list, tmp)
                    if input_list:
                        asp_file = open(asp_file_name, "a")
                        for i in input_list:
                            if i not in list_of_added_knowledge:
                                asp_file.write("\n" + ":- " + negate(i))
                                list_of_added_knowledge.append(i)
                        asp_file.close()

                        start = datetime.datetime.now()
                        ret = translator(asp_file_name, True)
                        print(datetime.datetime.now() - start)

                        if (ret.upper()).strip() != "SAT" and was_sat:
                            was_sat_inspection(asp_file_name, input_list)
                        else:
                            if not logs:
                                logs.append(add_point(diagnosis.converter(list_of_difference_red)))
                            else:
                                i = 1
                                tmp_set = set(add_point(diagnosis.converter(list_of_difference_red)))
                                while len(logs)-i > -1:
                                    tmp_set = tmp_set.difference(set(logs[len(logs)-i]))
                                    i += 1
                                logs.append(list(tmp_set))

                        first_run = False
                    else:
                        if list_of_added_knowledge:
                            print_red_blue_white()

            elif input_text.lower() == "delall":
                del_function(asp_file_name, list_of_added_knowledge)
                # print("all new predicates were deleted.")

            elif "lk" == input_text.lower():
                l = len(list_of_added_knowledge)
                if l == 1:
                    text = "element was added"
                else:
                    text = "elements were added"
                print('\033[1;33m' + str(l) + '\033[0m' + " " + text)
                for e in list_of_added_knowledge:
                    print (e + " "),
                print("")

            elif "#del" in input_text.lower():

                # input_text = "".join(input_text.split())
                input_text = input_text[4:]
                input_list = input_text.split("/")
                input_list = [e for e in input_list if e]
                input_list = add_point(handle_input_negation(input_list))
                del_function(asp_file_name, input_list)
                translator(asp_file_name, False)

            elif "#how" in input_text.lower():
                input_text = input_text[4:]
                input_list = input_text.split("/")
                input_list = [e for e in input_list if e]
                input_list = add_point(handle_input_negation(input_list))
                input_list = [e for e in input_list if e in allowed_entries]
                if input_list:
                    if input_list[0] in add_point(diagnosis.converter(list_of_difference_red)):
                        if not diagnosis.simple_inconsistency_chech(list_of_added_knowledge, input_list[0]):

                            # all minimal fixes
                            # diagnosis.create_original(list_of_added_knowledge, asp_file_name)
                            # minimal_fixes = HST.all_minimal(list_of_added_knowledge, input_list[0], asp_file_name)
                            # print_why_hitting(minimal_fixes)
                            # all minimal fixes

                            # delta = set(list_of_added_knowledge).union(add_point(diagnosis.converter(list_of_difference_white)))
                            # reasons = diagnosis.find_minimal_conflict_sets_optimized(list_of_added_knowledge, input_list[0], asp_file_name)

                            # with hitting sets

                            diagnosis.create_original(list_of_added_knowledge, asp_file_name)
                            start = datetime.datetime.now()
                            # conflict_sets = HST.cs_generator_2(list_of_added_knowledge, input_list[0], asp_file_name)
                            correction_sets = correctionset.cs_generator_2(list_of_added_knowledge, input_list[0], asp_file_name)
                            # conflict_sets = HST.cs_generator_py(list_of_added_knowledge, input_list[0], asp_file_name)
                            # reasons = HST.create_hs_dag(conflict_sets)

                            # reasons = HST.mcs_filter(conflict_sets)
                            print (datetime.datetime.now() - start)
                            print_why_hitting(correction_sets)

                            # with hitting sets

                            # test modified ASP
                            # diagnosis.create_original(list_of_added_knowledge, asp_file_name)
                            # start = datetime.datetime.now()
                            # to_keep = Magic_ASP.extend_original(list_of_added_knowledge, input_list[0], asp_file_name)
                            # print (datetime.datetime.now() - start)
                            # print_why_modified_asp(to_keep)
                            # test modified ASP

                            # good code
                            # diagnosis.create_original(list_of_added_knowledge, asp_file_name)
                            # start = datetime.datetime.now().replace(microsecond=0)
                            # reasons = diagnosis.build_all(list_of_added_knowledge, input_list[0], asp_file_name)
                            # print (datetime.datetime.now().replace(microsecond=0) - start)
                            # print_why(reasons)
                            # good code
                        else:
                            print("Because you have already selected " + negate(input_list[0]))
                    else:
                        print("The question must be about an element of the unavailable options ")

            elif "help" in input_text.lower():
                help_text = ["Literal", "ex: xx(y1,y2)\n",
                             "Extended Literal", "ex: #not xx(y1,y2)\n",
                             "Delete specific selections", "ex: #del xx(y1,y2)\n",
                             "Show Dependency", "ex: #what xx(y1,y2)\n",
                             "Generate Fixes", "ex: #how xx(y1,y2)\n",
                             "Delete All selections", "delall\n",
                             "List All selected options", "lk\n",
                             "Display Options", "show\n",
                             "Close the Program", "exit\n\n",
                             "*Note* Multiple entries and deletions must be separated by \"/\"", "\n"]
                for i in range(0, len(help_text), 2):
                    print('{:<30}  {:<30}'.format(help_text[i], help_text[i+1]))

            elif "show" in input_text.lower():
                print_red_blue_white()

            elif "#what" in input_text.lower():

                # input_text = "".join(input_text.split())
                input_text = input_text[5:]
                input_list = input_text.split("/")
                input_list = [e for e in input_list if e]
                input_list = add_point(handle_input_negation(input_list))
                if not what_if_delete():
                    print("This deletion will not affect the rest of the chosen options")


def init_predicates_names():
    """
    This function initialises the list of predicate names according to the first run of the program without the input of the user
    :return: 
    """
    global list_of_predicates_names
    list_of_predicates_names = []
    # should add "-" "not" "not -" to the names of predicates and add them to the list or not???
    for pr in list_of_predicates:
        list_of_predicates_names.append(pr.p_name)
    for i in range(len(list_of_predicates_names)):
        list_of_difference_blue.append([])
        list_of_difference_red.append([])
        list_of_difference_white.append([])
        tmp_prev_red.append([])


def what_if_delete():
    """
    this function returns the difference between a program befor some delletion and after it
    :return: 
    """
    global list_of_added_knowledge, asp_file_name, input_list, what
    start = '\033[95m'
    end = '\033[0m'
    diagnosis.create_original(list_of_added_knowledge, asp_file_name)
    tmp_asp_path = asp_file_name[:asp_file_name.rfind(os.sep) + 1]
    tmp_asp_file = tmp_asp_path + "what_if.txt"
    if os.path.exists(tmp_asp_file):
        os.remove(tmp_asp_file)

    copyfile(tmp_asp_path + "original_asp_program.txt", tmp_asp_file)

    with open(tmp_asp_file, "a") as tmp:
        for e in add_point([element for element in list_of_added_knowledge if element not in add_point(input_list)]):
            tmp.write(":- " + negate(e) + "\n")
    tmp.close()

    args = ['--enum-mode=cautious']
    prg = clingo.Control(args)
    try:
        prg.load(tmp_asp_file)
    except RuntimeError:
        return None
    prg.ground([("base", []), ("parts", [])])
    prg.solve(on_model=model_what_if)

    first = "Removing "
    for e in input_list:
        first += start + e[:len(e) - 1] + end + ", "
    first = first[:len(first) - 2]
    second = " will cause the deletion of "
    third = ""
    for e in list(set(add_point(diagnosis.converter(list_of_difference_white))).difference(add_point(what_if_white))):
        if e not in list_of_added_knowledge:
            third += start + e[:len(e) - 1] + end + ", "
    third = third[:len(third) - 2]
    if third:
        print(first + second + third)
        return True
    else:
        return False


def del_function(to_delete_from_file_name, to_delete_list, print_message=True):
    """
    This function deletes from the provided asp file every thing that is given in the input list 
    :param to_delete_from_file_name: 
    :param to_delete_list:
    :param print_message:
    :return: 
    """
    global list_of_added_knowledge, list_of_difference_red, list_of_predicates_not_to_negate, tmp_prev_white, logs
    to_delete_list = [":- " + negate(x) for x in to_delete_list]
    del_counter = 0
    fs = open(to_delete_from_file_name, "r")
    lines = fs.readlines()
    fs.close()
    fs = open(to_delete_from_file_name, "w")
    for line in lines:
        found = False
        line = line.strip()
        for inpt in handle_input_negation(to_delete_list):
            if line == inpt:
                found = True
                list_of_added_knowledge = [x for x in list_of_added_knowledge if x != negate(line.replace(":- ", ""))]
                del_counter += 1
                break
        if not found and line:
            fs.write(line + "\n")
    fs.close()

    # essential reset part for list_of_difference_red
    if len(list_of_added_knowledge) == 0:
        for i in range(len(list_of_difference_red)):
            list_of_difference_red[i] = []
        # reset list of cautious
        list_of_predicates_not_to_negate = []
        # rest previous white
        tmp_prev_white = []
        logs = []
    if print_message:
        if del_counter > 0:
            print("deleted!")
        else:
            print("nothing has been deleted!")


def update_configurables():
    """
    update the list of allowed entries
    :return: 
    """
    global list_of_predicates_not_to_negate, allowed_entries, asp_file_name
    allowed = []
    args = ['--enum-mode=brave']
    prg = clingo.Control(args)
    # print(prg.configuration)
    try:
        prg.load(asp_file_name)
    except RuntimeError as rte:
        print(rte)
        return "Parsing Problem"

    prg.ground([("base", []), ("parts", [])])
    ret = prg.solve(on_model=create_last_answer_set)
    if str(ret) == "SAT":
        model_function(last_answer_set[len(last_answer_set) - 1])
    for element in list_of_answer_sets[len(list_of_answer_sets) - 1]:
        for arguments in element.p_elements:
            predicate = element.p_name + "(" + arguments + ")."
            if predicate not in add_point(list_of_predicates_not_to_negate):
                ind = [x.p_index for x in list_of_indices if x.p_name == predicate[:predicate.index("(")]]
                if len(ind) > 0:
                    if predicate not in add_point(list_of_difference_red[ind[0]]):
                        allowed.append(predicate)
                else:
                    allowed.append(predicate)
    return allowed


def main():
    """
    
    :return: 
    """
    global was_sat, first_run, list_of_difference_red, list_of_difference_blue, tmp_prev_red, tmp_prev_blue, init_first_answer_set, list_of_indices, \
        list_of_difference_white, asp_file_name, tmp_prev_white

    parser = ArgumentParser()
    parser.add_argument("-f", dest="filename", required=True,
                        help="input file that contains the logic program", metavar="FILE",
                        type=lambda x: is_valid_file(parser, x))
    args = parser.parse_args()
    asp_file_name = args.filename
    start = datetime.datetime.now()
    res = translator(asp_file_name, True)
    print(datetime.datetime.now() - start)
    if conf_pr:
        if res == "SAT":
            was_sat = True
        else:
            was_sat = False

        # here is the second part of the program
        if was_sat:
            first_run = True

            handle_input(asp_file_name)
        else:
            was_unsat_inspection()


def is_valid_file(parser, arg):
    if not os.path.exists(arg):
        parser.error("The file %s does not exist!" % arg)
    else:
        return arg


if __name__ == '__main__':
    main()

