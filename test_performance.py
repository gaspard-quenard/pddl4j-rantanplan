import matplotlib.pyplot as plt
import numpy as np
from matplotlib.transforms import Affine2D
import logging
import os
from typing import List, Tuple
import subprocess
from enum import Enum
import shlex
import time
import pandas as pd

PATH_BENCHMARKS = [
    "benchmarks/blocksworld",
    "benchmarks/logistics",
    "benchmarks/gripper",
    "benchmarks/depots"
]

# Folder to write the results of the performance of the planner on the benchmarks
PATH_OUTPUT = "Results_benchmark"

# Command to build the library
BUILD_PDDL4J = "./gradlew build -PnoCheckStyle -PnoTest"

# Launch the jar lib 
LAUNCH_PDDL4J = "java -cp build/libs/pddl4j-4.0.0.jar"

# Path to HSP Planner in the PDDL4J lib
PATH_CLASS_HSP_IN_PDDL4J = "fr.uga.pddl4j.planners.statespace.HSP"

# Path to the Rantanplan planner in the PDDL4J lib
PATH_CLASS_RANTANPLAN_IN_PDDL4J = "fr.uga.pddl4j.planners.rantanplan.Rantanplan"

# Path to the VAL library
PATH_VAL_LIB = "src/test/resources/validators/validate-nux"

# Flag to validate the plan
CHECK_PLAN_VALIDITY = True

# Timeout of the planner in second
TIMEOUT_S = 3 * 60


class Planner(Enum):
    HSP = 0,
    RANTANPLAN = 1


def extract_plan_from_output(output_command: str) -> List[str]:
    """ Extract plan from the output of command line which launch a planner. If no plan is found, return None

    Args:
        output_command (str): stdout of the command line which launch a planner

    Returns:
        List[str]: The plan as a list of strings where each value of the list as index i correspond to the action of the plan at index i. Return None if no plan is found
    """

    all_lines_output = output_command.splitlines()

    try:
        idx_line_state_plan = all_lines_output.index(
            "found plan as follows:") + 2
        i = 0
        plan = []
        while (idx_line_state_plan + i < len(all_lines_output) and all_lines_output[idx_line_state_plan + i] != ''):
            plan.append(all_lines_output[idx_line_state_plan + i])
            i += 1

        return plan

    except ValueError:
        return None


def launch_planner(planner: Planner, full_path_file_domain: str, full_path_file_problem: str) -> Tuple[List[str], float]:
    """ Launch the planner specified and return the plan if found as well as the total runtime of the planner

    Args:
        planner (Planner): Planner to launch
        full_path_file_domain (str): Full path of the domain file
        full_path_file_problem (str): Full path of the problem file

    Returns:
        Tuple[List[str], float]: A tuple where the first argument contains the plan (or None if no plan is found), and the second argument contains the total runtime of the planner)
    """

    if (planner == Planner.RANTANPLAN):
        command = f"{LAUNCH_PDDL4J} {PATH_CLASS_RANTANPLAN_IN_PDDL4J} {full_path_file_domain} {full_path_file_problem}"

    elif (planner == Planner.HSP):
        command = f"{LAUNCH_PDDL4J} {PATH_CLASS_HSP_IN_PDDL4J} {full_path_file_domain} {full_path_file_problem}"

    else:
        logging.error("Incorrect planner provided")
        return (None, None)

    logging.info(f"Command: {command}")

    begin_time_command = time.time()
    try:
        output = subprocess.run(
            shlex.split(command), check=True, stdout=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)
        end_time_command = time.time()
        plan = extract_plan_from_output(output_command=output.stdout)
    # except subprocess.TimeoutExpired:
    except Exception as e:
        logging.error(f"Failed to find a plan with exception: {type(e).__name__}")
        end_time_command = time.time()
        plan = None

    # Keep only 3 decimals for the runtime
    total_runtime = round(end_time_command - begin_time_command, 3)

    return (plan, total_runtime)


def build_ppdl4J_lib() -> None:
    """
    Build the pddl4J library
    """

    output = subprocess.run(
        shlex.split(BUILD_PDDL4J), check=True, stdout=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)



def check_plan_validity(full_path_file_domain: str, full_path_file_problem: str, full_path_file_plan: str) -> bool:
    """Check if a plan is valid using the VAL library (see https://github.com/KCL-Planning/VAL)

    Args:
        full_path_file_domain (str): Full path of the domain file
        full_path_file_problem (str): Full path of the problem file
        full_path_file_plan (str): Full path of the plan file 

    Returns:
        bool: True if the plan is valid for this problem with this domain, False otherwise
    """

    command_check_plan = [
        f"./{PATH_VAL_LIB}",
        full_path_file_domain,
        full_path_file_problem,
        full_path_file_plan
    ]

    output = subprocess.run(
        command_check_plan, check=True, stdout=subprocess.PIPE, universal_newlines=True)

    if ("Plan valid" in output.stdout):
        return True
    else:
        return False


def generate_figures():
    """Generate figures to compare the results of the planners on two metrics: the total time spent to find a plan on a problem and the size of the plan generated. For each benchmark, there will be 1 file generated containing 2 figures: one for each of these metrics. Figures will be saved in the folder PATH_OUTPUT.
    """

    # Get all csv files in the output folder
    files_name = os.listdir(PATH_OUTPUT)
    csv_files_names = [file for file in files_name if file.endswith('.csv')]

    for file_name in csv_files_names:
        path_file_name = os.path.join(PATH_OUTPUT, file_name)

        benchmark_name = file_name.split('.')[0]

        data = pd.read_csv(path_file_name)

        # Sort data by hsp_total_run_time
        data.sort_values(["hsp_total_run_time"], axis=0,
                         ascending=[True], inplace=True)

        # Some clean of the data: Do not display bar of total run time of the planner if there is no plan found
        data.loc[(data['rantanplan_plan_size'] == 0), 'rantanplan_total_run_time'] = 0
        data.loc[(data['hsp_plan_size'] == 0), 'hsp_total_run_time'] = 0

        fig = plt.figure()
        ax1 = fig.add_subplot(211)

        abcisse = data["problem_name"].tolist()
        ordinate_hsp = data["hsp_total_run_time"].tolist()
        ordinate_rantanplan = data["rantanplan_total_run_time"].tolist()

        ax1.set_title(f"Time spent by planners on problems of benchmark \"{benchmark_name}\" to find a plan")
        ax1.set_xlabel("Problem name")
        ax1.set_ylabel("Time (s)")

        # Shift the bar of hsp a little to the left and the bar of rantanplan a little to the right
        # to be able to see both bar for each problem
        shiftBarLeft = Affine2D().translate(-0.1, 0.0) + ax1.transData
        shiftBarRight = Affine2D().translate(+0.1, 0.0) + ax1.transData
        ax1.bar(abcisse, ordinate_hsp, facecolor='b',
                label="HSP", transform=shiftBarLeft, width=0.2)
        ax1.bar(abcisse, ordinate_rantanplan, facecolor='r',
                label="Rantanplan", transform=shiftBarRight, width=0.2)

        plt.legend(loc='upper left')

        ax2 = fig.add_subplot(212)

        shiftBarLeft = Affine2D().translate(-0.1, 0.0) + ax2.transData
        shiftBarRight = Affine2D().translate(+0.1, 0.0) + ax2.transData

        abcisse = data["problem_name"].tolist()
        ordinate_hsp = data["hsp_plan_size"].tolist()
        ordinate_rantanplan = data["rantanplan_plan_size"].tolist()

        ax2.set_title(f"Size of plan generated by planners on problems of benchmark \"{benchmark_name}\"")
        ax2.set_xlabel("Problem name")
        ax2.set_ylabel("Size plan")

        ax2.bar(abcisse, ordinate_hsp, facecolor='b',
                label="HSP", transform=shiftBarLeft, width=0.2)
        ax2.bar(abcisse, ordinate_rantanplan, facecolor='r',
                label="Rantanplan", transform=shiftBarRight, width=0.2)

        plt.legend(loc='upper left')

        path_figure = os.path.join(PATH_OUTPUT, f"figure_result_{benchmark_name}.png")

        logging.info(f"Save figure {path_figure}")

        # Set the figure width enough to prevent xlabel from overlapping
        fig.set_size_inches((18, 11), forward=False)

        plt.savefig(path_figure)
        # plt.show()


if __name__ == '__main__':

    # Initialize logging
    logging.basicConfig(
        format='%(asctime)s %(levelname)s:%(message)s', level=logging.DEBUG)

    # First, build the library
    logging.info("Build the pddl4 lib")
    build_ppdl4J_lib()

    for path_benchmark in PATH_BENCHMARKS:

        name_benchmark = path_benchmark.split('/')[-1]
        logging.info(
            f"Test benchmark {name_benchmark}")

        # Create the file to write results if not exist
        file_to_write_result = os.path.join(
            PATH_OUTPUT, "{name_benchmark}.csv".format(name_benchmark=name_benchmark))
        if (not os.path.exists(file_to_write_result)):
            # Initialize the file by writing the name of all the columns
            with open(file_to_write_result, 'a') as f:
                f.write(
                    "benchmark_name,problem_name,rantanplan_plan_size,rantanplan_total_run_time,hsp_plan_size,hsp_total_run_time\n")

        # Load all the problems
        files_in_benchmark = sorted(os.listdir(path_benchmark))

        if ("domain.pddl" not in files_in_benchmark):
            logging.error(
                f"Domain file does not exist for benchmark path: {path_benchmark}. Skip this benchmark")
            continue

        logging.info(f"Domain file found for benchmark path: {path_benchmark}")

        full_path_benchmark = os.path.abspath(path_benchmark)

        full_path_file_domain = os.path.join(
            full_path_benchmark, "domain.pddl")

        files_in_benchmark.remove("domain.pddl")

        # Keep only the first 15 level of each benchmark
        files_in_benchmark = files_in_benchmark[:15]

        for problem_file in files_in_benchmark:

            with open(file_to_write_result, 'r') as f:
                skip_problem = False
                lines = f.readlines()
                for line in lines:
                    if (f"{name_benchmark},{problem_file}" in line):
                        logging.info(f"Problem {problem_file} of benchmark: {name_benchmark} already done")
                        skip_problem = True
                        break

                if (skip_problem):
                    continue

            full_path_file_problem = os.path.join(
                full_path_benchmark, problem_file)

            logging.info("For problem: {full_path_file_problem}".format(
                         full_path_file_problem=full_path_file_problem))

            logging.info("Launch Rantanplan planner")
            plan_rantanplan, total_run_time_rantanplan = launch_planner(planner=Planner.RANTANPLAN,
                                                          full_path_file_domain=full_path_file_domain,
                                                          full_path_file_problem=full_path_file_problem)

            if (plan_rantanplan == None):
                logging.error("Failed to find a plan for problem {problem_name} of benchmark {benchmark_name} with Rantanplan planner".format(
                    problem_name=problem_file, benchmark_name=path_benchmark))
                plan_rantanplan = []

            elif (CHECK_PLAN_VALIDITY):
                # Write the plan into a file to be able to check the plan validity with VAL
                plan_file_name = "tmp_plan_{}".format(problem_file)
                full_path_file_plan = os.path.join(
                    full_path_benchmark, plan_file_name)
                with open(full_path_file_plan, 'w') as f:
                    f.writelines(plan_rantanplan)

                plan_is_valid = check_plan_validity(full_path_file_domain=full_path_file_domain,
                                                    full_path_file_problem=full_path_file_problem,
                                                    full_path_file_plan=full_path_file_plan)

                # Delete the plan file
                os.remove(os.path.join(full_path_benchmark, plan_file_name))

                if (not plan_is_valid):
                    logging.error(f"Rantanplan Plan is invalid for problem {problem_file} of benchmark {path_benchmark}")
                    exit(1)
                else:
                    logging.info(f"Rantanplan Plan is valid for problem {problem_file} of benchmark {path_benchmark}")

            logging.info(f"Size plan: {len(plan_rantanplan)}, total time: {total_run_time_rantanplan} s")

            logging.info("Launch HSP planner")
            plan_hsp, total_run_time_hsp = launch_planner(Planner.HSP, full_path_file_domain=full_path_file_domain,
                                                          full_path_file_problem=full_path_file_problem)

            if (plan_hsp == None):
                logging.error(f"Failed to find a plan for problem {problem_file} of benchmark {path_benchmark} with HSP planner")
                plan_hsp = []

            logging.info(f"Size plan: {len(plan_hsp)}, total time: {total_run_time_hsp} s")

            with open(file_to_write_result, 'a') as f:
                line_to_write = f"{name_benchmark},{problem_file},{len(plan_rantanplan)},{total_run_time_rantanplan},{len(plan_hsp)},{total_run_time_hsp}\n"
                f.write(line_to_write)

        logging.info("Generate figure")
        generate_figures()
