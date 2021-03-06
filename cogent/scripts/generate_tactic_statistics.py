#!/usr/bin/env python3

#
# Copyright 2019, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)
#

import sys, json
from statistics import mean, median

#
# Usage: Take the output log generated by mk_ttsplit_tacs_final in cogent/isa/CogentHelper.thy
#        and use it as input to this file (usually ~/TypeProofTactic.json)
#
# Then run: ./generate_tactic_statistics.py TypeProofTactic.json [outfile]
#
# Optionally include outfile to have statistics logged in json format.
#


def make_stats_obj(num_list):
    obj = {}
    obj['average'] = mean(num_list)
    obj['min']     = min(num_list)
    obj['max']     = max(num_list)
    obj['median']  = median(num_list)
    obj['total']   = sum(num_list)
    obj['amount']  = len(num_list)

    return obj

if len(sys.argv) < 2:
    print("Usage: " + sys.argv[0] + " filename [OPTIONS] [outfile]")
    print("Where OPTIONS is one of: ")
    print("\t--plot - Create GNUPlot plotting data in outfile")
    print("\t--json - Create JSON transformed data in outfile")
    exit(1)

PLOT = False
JSON = False
OUTFILE = ""
INFILE = sys.argv[1]
if len(sys.argv) == 4:
    option  = sys.argv[2]
    OUTFILE = sys.argv[3]

    if option == "--plot":
        PLOT = True
    elif option == "--json":
        JSON = True
    else:
        print("Error: '" + option + "' is not a valid option")
        exit(1)

try:
    f = open(INFILE, 'r')
    content = f.readlines()

    tactic_times = {}

    for line in content:
        data = json.loads(line)
        [tactic_name, type_name] = data['tacticName'].split(':')
        if not tactic_name in tactic_times:
            tactic_times[tactic_name] = {}
        if not type_name in tactic_times[tactic_name]:
            tactic_times[tactic_name][type_name] = []

        tactic_times[tactic_name][type_name].append(data['time'])

    final_stats = {}
    all_exprs = {} # Keep track of all existing expressions

    total_per_tactic = {}
    # print stats
    for key in tactic_times.keys():
        final_stats[key] = {}
        print("tactic '{}':".format(key))
        row_format ="{:>15}" * 7
        print(row_format.format("Type", 
                                *sorted(["Amount"] + list(map(lambda x: x + " (μs)",["Min","Average","Median","Max", "Total"]))) )
                                )

        total = []
        for expr in sorted(tactic_times[key].keys()):
            all_exprs[expr] = True
            cpu = [d['cpu'] for d in tactic_times[key][expr]]

            final_stats[key][expr] = {
                    "cpu":      make_stats_obj(cpu)
                    #"elapsed":  make_stats_obj(elapsed),
                    #"gc":       make_stats_obj(gc),
                }

            total += cpu

            for t in ["cpu"]:
                stat_obj = final_stats[key][expr][t.lower()]
                nums = [str(int(x)) for x in [stat_obj[key] for key in sorted(stat_obj.keys())]]
                print(row_format.format(expr, *nums))
        total_stat = make_stats_obj(total)
        print(row_format.format("Total", *[str(int(total_stat[x])) for x in sorted(total_stat.keys())]), '\n')
        total_per_tactic[key] = sum(total)

    total_of_all = sum([total_per_tactic[k] for k in total_per_tactic])

    print("Overall totals (μs): ")
    print("\tTotal Time: " + str(total_of_all))
    for k in total_per_tactic:
        print("\t" + k + ": " + str(round(float(total_per_tactic[k])/total_of_all, 3)*100) + "%" + ", " + str(total_per_tactic[k]))


    # Log stats if outfile present
    if JSON:
        with open(OUTFILE, 'w') as out:
            stat_str = json.dumps(final_stats)
            out.write(stat_str)
    # make gnuplot data
    if PLOT:
        with open(OUTFILE, 'w') as out:
            out.write("Tactic")
            for key in sorted(final_stats.keys()):
                out.write("\t\t" + key)
            out.write('\n')

            for expr in sorted(all_exprs.keys()):
                out.write(expr)
                for key in sorted(final_stats.keys()):
                    if expr not in final_stats[key]:
                        out.write("\t\t0")
                    else:
                        out.write("\t\t" + str(final_stats[key][expr]['cpu']['total']))
                out.write('\n')


except FileNotFoundError:
    print("File '" + sys.argv[1] + "' not found.")
