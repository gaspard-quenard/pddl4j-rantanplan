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
    "src/test/resources/benchmarks/hddl/ipc2020/miconic",
    "src/test/resources/benchmarks/hddl/ipc2020/transport",
    "src/test/resources/benchmarks/hddl/ipc2020/gripper",
    "src/test/resources/benchmarks/hddl/ipc2020/rover",
    "src/test/resources/benchmarks/hddl/ipc2020/barman",
    "src/test/resources/benchmarks/hddl/ipc2020/childsnack",    
]

# Folder to write the results of the performance of the planner on the benchmarks
PATH_OUTPUT = "Results_benchmark_TreeRex"

# Command to build the library
BUILD_PDDL4J = "./gradlew build -PnoCheckStyle -PnoTest"

# Launch the jar lib
LAUNCH_PDDL4J = "java -cp build/libs/pddl4j-4.0.0.jar"

# Path to TreeRex Planner in the PDDL4J lib
PATH_CLASS_TREEREX_IN_PDDL4J = "fr.uga.pddl4j.planners.treerex_smt.TreeRex"


# Timeout of the planner in second
TIMEOUT_S = 5 * 60


class Planner(Enum):
    HSP = 0,
    RANTANPLAN = 1


class TreeRex_optimimzations(Enum):
    SASPlus = 0
    ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER = 1


CONFIGURATIONS_TO_USE = [
    [],
    [TreeRex_optimimzations.SASPlus],
    [TreeRex_optimimzations.SASPlus,
        TreeRex_optimimzations.ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER]
]

dict_configuration_option_to_command_line = {
    TreeRex_optimimzations.SASPlus: "--use-sas-plus",
    TreeRex_optimimzations.ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER: "--use-one-var-per-action-layer-element"
}


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


def launch_planner(full_path_file_domain: str, full_path_file_problem: str, configuration_to_use: List) -> Tuple[List[str], float]:
    """ Launch the TreeRex planner with the configuration specified and return the plan if found as well as the total runtime of the planner

    Args:
        full_path_file_domain (str): Full path of the domain file
        full_path_file_problem (str): Full path of the problem file
        configuration_to_use: Configuration to use for the planner

    Returns:
        Tuple[List[str], float]: A tuple where the first argument contains the plan (or None if no plan is found), and the second argument contains the total runtime of the planner)
    """

    command = f"{LAUNCH_PDDL4J} {PATH_CLASS_TREEREX_IN_PDDL4J} {full_path_file_domain} {full_path_file_problem}"
    for conf in configuration_to_use:
        command += f" {dict_configuration_option_to_command_line[conf]}"

    logging.info(f"Command: {command}")

    begin_time_command = time.time()
    try:
        output = subprocess.run(
            shlex.split(command), check=True, stdout=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)
        end_time_command = time.time()
        plan = extract_plan_from_output(output_command=output.stdout)
    # except subprocess.TimeoutExpired:
    except Exception as e:
        logging.error(
            f"Failed to find a plan with exception: {type(e).__name__}")
        end_time_command = time.time()
        plan = None
        return (plan, 0, 0, 0)

    lines = output.stdout.split('\n')
    # Make sure that the plan is found and correct
    if (plan != None and not "Plan is valid !" in lines):
        logging.error("Plan found is incorrect")
        plan = None

    # Get the preprocessing time, encoding time and solving time from the output
    try:
        preprocessing_time_ms = int([line for line in lines if line.startswith("Preprocessing time (ms):")][0].split()[-1])
        encoding_time_ms = int([line for line in lines if line.startswith("Encoding time (ms):")][0].split()[-1])
        solving_time_ms = int([line for line in lines if line.startswith("Solving time (ms):")][0].split()[-1])
    except Exception as e:
        logging.error("Failed to get preprocessing time, encoding time and solving time from the output...")
        preprocessing_time_ms = 0
        encoding_time_ms = 0
        solving_time_ms = 0

    return (plan, preprocessing_time_ms, encoding_time_ms, solving_time_ms)


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
    """Generate figures to compare the results of the planners on two metrics: the total time spent to find a plan on a problem and the size of the plan generated. 
    For each benchmark, there will be 1 file generated containing 2 figures: one for each of these metrics. Figures will be saved in the folder PATH_OUTPUT.
    """

    # Get all csv files in the output folder
    files_name = os.listdir(PATH_OUTPUT)
    csv_files_names = [file for file in files_name if file.endswith('.csv')]

    


    for file_name in csv_files_names:

        print(f"Generate figure for {file_name}")

        path_file_name = os.path.join(PATH_OUTPUT, file_name)

        benchmark_name = file_name.split('.')[0]

        data = pd.read_csv(path_file_name)

        # Get all the differents configurations that was used in the test
        configurations_used = data['optimizations_used'].unique()
        

        # Create the configuration fot each
        dict_conf_used_to_df = {}

        for conf in configurations_used:
            if pd.isna(conf):
                dict_conf_used_to_df['no_conf'] = data[data['optimizations_used'].isna()]
            else:
                dict_conf_used_to_df[conf] = data[data['optimizations_used'] == conf]

        # Sort data by hsp_total_run_time
        # data.sort_values(["hsp_total_run_time"], axis=0,
        #                  ascending=[True], inplace=True)

        # Some clean of the data: Do not display bar of total run time of the planner if there is no plan found
        # data.loc[(data['plan_size'] == 0),
        #          'rantanplan_total_run_time'] = 0
        # data.loc[(data['hsp_plan_size'] == 0), 'hsp_total_run_time'] = 0

        # We will encode the initialization time, encoding time and solver time and total time in 4 different graph
        fields_to_display = ["treerex_initialization_time", "encoding_time", "solver_time"]

        fig = plt.figure()
        fig.suptitle(f"On domain {benchmark_name}")
        ax1 = fig.add_subplot(221)

        abcisse = [name.split('.')[0] for name in dict_conf_used_to_df['no_conf']["problem_name"].tolist()]
        init_time_ordinate_no_conf = dict_conf_used_to_df['no_conf']["treerex_initialization_time"].tolist()
        init_time_ordinate_SASplus = dict_conf_used_to_df['SASPlus']["treerex_initialization_time"].tolist()
        init_time_ordinate_SASplus_one_var_actionper_layer_position = dict_conf_used_to_df['SASPlus+ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER']["treerex_initialization_time"].tolist()

        ax1.set_title(
            "Initialization time")
        ax1.set_xlabel("Problem name")
        ax1.set_ylabel("Time (ms)")

        ax1.scatter(abcisse, init_time_ordinate_no_conf, label="no_conf")
        ax1.plot(abcisse, init_time_ordinate_no_conf) # Use the plot to connect scatterplot points
        ax1.scatter(abcisse, init_time_ordinate_SASplus, label="SASPlus")
        ax1.plot(abcisse, init_time_ordinate_SASplus)
        ax1.scatter(abcisse, init_time_ordinate_SASplus_one_var_actionper_layer_position, label="ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER")
        ax1.plot(abcisse, init_time_ordinate_SASplus_one_var_actionper_layer_position)

        plt.legend(loc='upper left')

        ax2 = fig.add_subplot(222)

        abcisse = [name.split('.')[0] for name in dict_conf_used_to_df['no_conf']["problem_name"].tolist()]
        encode_time_ordinate_no_conf = dict_conf_used_to_df['no_conf']["encoding_time"].tolist()
        encode_time_ordinate_SASplus = dict_conf_used_to_df['SASPlus']["encoding_time"].tolist()
        encode_time_ordinate_SASplus_one_var_actionper_layer_position = dict_conf_used_to_df['SASPlus+ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER']["encoding_time"].tolist()

        ax2.set_title(
            f"Encoding time")
        ax2.set_xlabel("Problem name")
        ax2.set_ylabel("Time (ms)")

        ax2.scatter(abcisse, encode_time_ordinate_no_conf, label="no_conf")
        ax2.plot(abcisse, encode_time_ordinate_no_conf) # Use the plot to connect scatterplot points
        ax2.scatter(abcisse, encode_time_ordinate_SASplus, label="SASPlus")
        ax2.plot(abcisse, encode_time_ordinate_SASplus)
        ax2.scatter(abcisse, encode_time_ordinate_SASplus_one_var_actionper_layer_position, label="ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER")
        ax2.plot(abcisse, encode_time_ordinate_SASplus_one_var_actionper_layer_position)

        plt.legend(loc='upper left')

        ax3 = fig.add_subplot(223)

        abcisse = [name.split('.')[0] for name in dict_conf_used_to_df['no_conf']["problem_name"].tolist()]
        solver_time_ordinate_no_conf = dict_conf_used_to_df['no_conf']["solver_time"].tolist()
        solver_time_ordinate_SASplus = dict_conf_used_to_df['SASPlus']["solver_time"].tolist()
        solver_time_ordinate_SASplus_one_var_actionper_layer_position = dict_conf_used_to_df['SASPlus+ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER']["solver_time"].tolist()

        ax3.set_title(
            f"Solver time")
        ax3.set_xlabel("Problem name")
        ax3.set_ylabel("Time (ms)")

        ax3.scatter(abcisse, solver_time_ordinate_no_conf, label="no_conf")
        ax3.plot(abcisse, solver_time_ordinate_no_conf) # Use the plot to connect scatterplot points
        ax3.scatter(abcisse, solver_time_ordinate_SASplus, label="SASPlus")
        ax3.plot(abcisse, solver_time_ordinate_SASplus)
        ax3.scatter(abcisse, solver_time_ordinate_SASplus_one_var_actionper_layer_position, label="ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER")
        ax3.plot(abcisse, solver_time_ordinate_SASplus_one_var_actionper_layer_position)

        plt.legend(loc='upper left')

        # Make a final curve with full time
        ax4 = fig.add_subplot(224)

        abcisse = [name.split('.')[0] for name in dict_conf_used_to_df['no_conf']["problem_name"].tolist()]
        full_time_ordinate_no_conf = np.asarray(init_time_ordinate_no_conf) + np.asarray(encode_time_ordinate_no_conf) + np.asarray(solver_time_ordinate_no_conf)
        full_time_ordinate_SASplus = np.asarray(init_time_ordinate_SASplus) + np.asarray(encode_time_ordinate_SASplus) + np.asarray(solver_time_ordinate_SASplus)
        full_time_ordinate_SASplus_one_var_actionper_layer_position = np.asarray(init_time_ordinate_SASplus_one_var_actionper_layer_position) + np.asarray(encode_time_ordinate_SASplus_one_var_actionper_layer_position) + np.asarray(solver_time_ordinate_SASplus_one_var_actionper_layer_position)

        ax4.set_title(
            f"Full time")
        ax4.set_xlabel("Problem name")
        ax4.set_ylabel("Time (ms)")

        ax4.scatter(abcisse, full_time_ordinate_no_conf, label="no_conf")
        ax4.plot(abcisse, full_time_ordinate_no_conf) # Use the plot to connect scatterplot points
        ax4.scatter(abcisse, full_time_ordinate_SASplus, label="SASPlus")
        ax4.plot(abcisse, full_time_ordinate_SASplus)
        ax4.scatter(abcisse, full_time_ordinate_SASplus_one_var_actionper_layer_position, label="ONE_VAR_ACTION_FOR_EACH_POSITION_LAYER")
        ax4.plot(abcisse, full_time_ordinate_SASplus_one_var_actionper_layer_position)

        plt.legend(loc='upper left')

        path_figure = os.path.join(
            PATH_OUTPUT, f"figure_result_{benchmark_name}.png")

        logging.info(f"Save figure {path_figure}")

        # Set the figure width enough to prevent xlabel from overlapping
        fig.set_size_inches((18, 11), forward=False)

        plt.savefig(path_figure)
        plt.show()


if __name__ == '__main__':

    # Initialize logging
    logging.basicConfig(
        format='%(asctime)s %(levelname)s:%(message)s', level=logging.DEBUG)

    generate_figures()
    exit(0)

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
                    "benchmark_name,problem_name,optimizations_used,treerex_initialization_time,encoding_time,solver_time,plan_size\n")

        # Load all the problems
        files_in_benchmark = sorted(os.listdir(path_benchmark))

        # Remove all files which do not end with hddl
        files_in_benchmark = [f for f in files_in_benchmark if f.endswith("hddl")]

        if ("domain.hddl" not in files_in_benchmark):
            logging.error(
                f"Domain file does not exist for benchmark path: {path_benchmark}. Skip this benchmark")
            continue

        logging.info(f"Domain file found for benchmark path: {path_benchmark}")

        full_path_benchmark = os.path.abspath(path_benchmark)

        full_path_file_domain = os.path.join(
            full_path_benchmark, "domain.hddl")

        files_in_benchmark.remove("domain.hddl")

        # Keep only the first 10 level of each benchmark
        files_in_benchmark = files_in_benchmark[:10]

        for problem_file in files_in_benchmark:

            for configuration_to_use in CONFIGURATIONS_TO_USE:

                full_name_configuration = "+".join(
                    [opt.name for opt in configuration_to_use])

                with open(file_to_write_result, 'r') as f:
                    skip_problem = False
                    lines = f.readlines()
                    for line in lines:
                        if (f"{name_benchmark},{problem_file},{full_name_configuration}" in line):
                            logging.info(
                                f"Problem {problem_file} of benchmark: {name_benchmark} already done with optimization {full_name_configuration}")
                            skip_problem = True
                            break

                    if (skip_problem):
                        continue

                full_path_file_problem = os.path.join(
                    full_path_benchmark, problem_file)

                logging.info(f"For problem: {full_path_file_problem}")

                logging.info(
                    f"Launch TreeRex planner with configuration: {full_name_configuration}")
                plan, preprocessing_time_ms, encoding_time_ms, solving_time_ms = launch_planner(
                    full_path_file_domain=full_path_file_domain,
                    full_path_file_problem=full_path_file_problem,
                    configuration_to_use=configuration_to_use)

                if (plan == None):
                    logging.error(
                        f"Failed to find a plan for problem {problem_file} of benchmark {path_benchmark} with TreeRex planner")
                    plan = []


                logging.info(
                    f"Size plan: {len(plan)}, preprocessing time: {preprocessing_time_ms} ms, encoding time: {encoding_time_ms} ms, solving time: {solving_time_ms} ms")

                with open(file_to_write_result, 'a') as f:
                    line_to_write = f"{name_benchmark},{problem_file},{full_name_configuration},{preprocessing_time_ms},{encoding_time_ms},{solving_time_ms},{len(plan)}\n"
                    f.write(line_to_write)

        # logging.info("Generate figure")
        # generate_figures()
