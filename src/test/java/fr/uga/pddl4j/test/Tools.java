package fr.uga.pddl4j.test;

import fr.uga.pddl4j.parser.ErrorManager;
import fr.uga.pddl4j.parser.Message;
import fr.uga.pddl4j.parser.PDDLParser;
import fr.uga.pddl4j.parser.PDDLProblem;
import fr.uga.pddl4j.parser.PDDLRequireKey;
import fr.uga.pddl4j.parser.ParsedProblem;
import fr.uga.pddl4j.problem.ADLProblem;
import fr.uga.pddl4j.problem.HTNProblem;
import fr.uga.pddl4j.problem.NumericProblem;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.SimpleTemporalProblem;
import org.junit.Assert;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Static class that contains all shared method for manipulate the benchmark
 * directory structure.
 *
 * @author C. Gerard
 * @author D. Pellier
 * @version 1.1 - 23.06.16
 */
public abstract class Tools {

    /**
     * The path of the pddl benchmarks files.
     */
    public static final String PDDL_BENCH_DIR = "src/test/resources/benchmarks/pddl" + File.separator;

    /**
     * The path of the HDDL benchmarks files.
     */
    public static final String HDDL_BENCH_DIR = "src/test/resources/benchmarks/hddl" + File.separator;

    /**
     * PDDL files extension.
     */
    public static final String PDDL_EXT = ".pddl";

    /**
     * PDDL files extension.
     */
    public static final String HDDL_EXT = ".hddl";

    /**
     * PDDL4J output plan extension for KCL validator format.
     */
    public static final String VAL_EXT = ".val";

    /**
     * The PDDL domain file name.
     */
    public static final String PDDL_DOMAIN = "domain" + Tools.PDDL_EXT;

    /**
     * The HDDL domain file name.
     */
    public static final String HDDL_DOMAIN = "domain" + Tools.HDDL_EXT;

    /**
     * The path to PDDL_VAL.
     */
    public static final String PDDL_VAL = "src/test/resources/validators/validate";

    /**
     * The path to HDDL_VAL.
     */
    public static final String HDDL_VAL = "src/test/resources/validators/pandaPIParser";

    /**
     * Check if benchmark are already here.
     *
     * @param path the benchmark directory path
     * @return true if the benchmark file exist
     */
    public static boolean isBenchmarkExist(String path) {
        return new File(path).exists();
    }

    /**
     * Clean all val formatted plan from the current directory and all its subdirectories.
     *
     * @param localTestPath the current path to clean up
     */
    public static void cleanValPlan(String localTestPath) {
        File dir = new File(localTestPath);
        File[] files = dir.listFiles((dir1, name) -> name.endsWith(".val"));

        if (files != null) {
            for (File file : files) {
                try {
                    Files.deleteIfExists(FileSystems.getDefault().getPath(localTestPath, file.getName()));
                    System.out.println("Deleting " + localTestPath + file.getName());
                } catch (IOException ioEx) {
                    ioEx.printStackTrace();
                }
            }
            System.out.println();
        }
    }

    /**
     * Parse domain and problem files and return the associated coded problem.
     *
     * @param domainFile  the domain file to be tested.
     * @param problemFile the file file to be tested.
     * @return a coded problem from the parsing file
     */
    public static ADLProblem generateCodedProblem(String domainFile, String problemFile) {
        try {
            final File domain = new File(domainFile);
            final File problem = new File(problemFile);
            PDDLParser parser = new PDDLParser();
            ParsedProblem parsedProblem = parser.parse(domain, problem);
            ErrorManager errorManager = parser.getErrorManager();
            if (errorManager.isEmpty()) {
                return new ADLProblem(parsedProblem);
            }
        } catch (IOException ioExcepion) {
            System.err.println(ioExcepion + " test files not found !");
        }
        return null;
    }

    /**
     * Change the permissions for PDDL_VAL file (add read, write and execute).
     */
    public static void changeVALPerm() {
        final File val = new File(Tools.PDDL_VAL);
        if (val.exists() && (Tools.isUnix() || Tools.isMac())) {
            val.setReadable(true);
            val.setExecutable(true);
        }
    }

    /**
     * Remove the extension of a filename.
     *
     * @param fileName the name of the file
     * @return the filename of the file without extension
     */
    public static String removeExtension(String fileName) {
        final Pattern ext = Pattern.compile("(?<=.)\\.[^.]+$");
        return ext.matcher(fileName).replaceAll("");
    }

    /**
     * Count the number of validated plans.
     *
     * @param outputVal the output of PDDL_VAL
     * @return the number of validated plans
     */
    public static int numberValidatedPlans(String outputVal) {
        int i = 0;
        final Pattern p = Pattern.compile("Plan valid");
        final Matcher m = p.matcher(outputVal);
        while (m.find()) {
            i++;
        }
        return i;
    }

    /**
     * Read the content of a file.
     *
     * @param path     the path to the file
     * @param encoding encoding of the file
     * @return the content of the file encoded
     * @throws IOException if an error occurs when reading file from path.
     */
    public static String readFile(String path, Charset encoding) throws IOException {
        byte[] encoded = Files.readAllBytes(Paths.get(path));
        return new String(encoded, encoding);
    }

    /**
     * Validate output plans.
     *
     * @param currentTestPath the current sub dir to test.
     * @throws Exception if something wrong.
     */
    public static void validatePDDLPlans(String currentTestPath) throws Exception {
        final String domain = currentTestPath + "domain.pddl";
        File dir = new File(currentTestPath);
        File[] files = dir.listFiles((dir1, name) -> name.endsWith(".val"));

        if (files != null) {
            final StringBuilder output = new StringBuilder();

            for (File valfile : files) {
                final String problem = currentTestPath + Tools.removeExtension(valfile.getName()) + ".pddl";
                String target;
                if (isWindows()) {
                    target = Tools.PDDL_VAL + "-win.exe -v " + domain + " " + problem + " " + valfile;
                } else if (isMac()) {
                    target = Tools.PDDL_VAL + "-osx -v " + domain + " " + problem + " " + valfile;
                } else {
                    target = Tools.PDDL_VAL + "-nux -v " + domain + " " + problem + " " + valfile;
                }

                final Runtime rt = Runtime.getRuntime();
                final Process proc = rt.exec(target);
                proc.waitFor();

                String line;
                final InputStreamReader inputStreamReader = new InputStreamReader(proc.getInputStream(),
                    StandardCharsets.UTF_8);
                final BufferedReader reader = new BufferedReader(inputStreamReader);
                try {
                    while ((line = reader.readLine()) != null) {
                        output.append(line + "\n");
                    }
                } catch (IOException ioe) {
                    ioe.printStackTrace();
                } finally {
                    reader.close();
                    inputStreamReader.close();
                    proc.getInputStream().close();
                }
            }

            final int number = Tools.numberValidatedPlans(output.toString());
            System.out.println("\n-- PDDL_VAL on " + currentTestPath);
            System.out.println("   Plans found: " + files.length);
            System.out.println("   Plans validated: " + number);
            System.out.println("--");
            Assert.assertEquals(files.length, number);
        }

        Tools.cleanValPlan(currentTestPath);

    }


    /**
     * Validate HDDL output plans.
     *
     * @param currentTestPath the current sub dir to test.
     * @throws Exception if something wrong.
     */
    public static void validateHDDLPlans(String currentTestPath) throws Exception {
        final String domain = currentTestPath + Tools.HDDL_DOMAIN;
        File dir = new File(currentTestPath);
        File[] files = dir.listFiles((dir1, name) -> name.endsWith(Tools.VAL_EXT));

        if (files != null) {
            final StringBuilder output = new StringBuilder();
            int nbValidated = 0;
            for (File valfile : files) {
                final String problem = currentTestPath + Tools.removeExtension(valfile.getName()) + Tools.HDDL_EXT;
                String target;
                if (Tools.isWindows()) {
                    target = Tools.HDDL_VAL + "-win.exe -v " + domain + " " + problem + " " + valfile;
                } else if (Tools.isMac()) {
                    target = Tools.HDDL_VAL + "-osx -v " + domain + " " + problem + " " + valfile;
                } else {
                    target = Tools.HDDL_VAL + "-nux -v " + domain + " " + problem + " " + valfile;
                }
                final Runtime rt = Runtime.getRuntime();
                final Process process = rt.exec(target);
                process.waitFor();

                String line;
                final InputStreamReader inputStreamReader = new InputStreamReader(process.getInputStream(),
                    StandardCharsets.UTF_8);
                final BufferedReader reader = new BufferedReader(inputStreamReader);
                boolean validated = true;
                try {
                    while ((line = reader.readLine()) != null && validated) {
                        validated = line.indexOf("false") != 1;
                        output.append(line + "\n");
                    }
                    if (validated) {
                        nbValidated++;
                    }
                } catch (IOException ioe) {
                    ioe.printStackTrace();
                } finally {
                    reader.close();
                    inputStreamReader.close();
                    process.getInputStream().close();
                }
            }

            final int number = Tools.numberValidatedPlans(output.toString());
            System.out.println("\n-- HDDL Plan Validator on " + currentTestPath);
            System.out.println("   Plans found: " + files.length);
            System.out.println("   Plans validated: " + nbValidated);
            System.out.println("--");
            Assert.assertEquals(files.length, nbValidated);
        }
        Tools.cleanValPlan(currentTestPath);

    }

    /**
     * Encode problems targeted in currentTestPath directory and check if they are solvable.
     *
     * @param currentTestPath the current directory to test.
     * @param extension the extension of the file.
     */
    public static void instantiate(String currentTestPath, String extension) {
        String currentDomain = currentTestPath + "domain" + extension;
        boolean oneDomainPerProblem = false;
        String problemFile;
        String currentProblem;

        // Counting the number of problem files
        File[] pbFileList = new File(currentTestPath)
            .listFiles((dir, name) -> name.startsWith("p") && name.endsWith(extension) && !name.contains("dom"));

        int nbTest = 0;
        if (pbFileList != null) {
            nbTest = pbFileList.length;
        }

        // Check if there is on domain per problem or a shared domain for all
        if (!new File(currentDomain).exists()) {
            oneDomainPerProblem = true;
        }

        System.out.println("Instantiation: Test on " + currentTestPath);
        int fillLength = Math.max(Integer.toString(nbTest).length(), 2);
        for (int i = 1; i < nbTest + 1; i++) {
            problemFile = String.format("p%0" + fillLength + "d" + extension, i);
            currentProblem = currentTestPath + problemFile;
            if (oneDomainPerProblem) {
                currentDomain = currentTestPath + problemFile.split(".p")[0] + "-" + "domain" + extension;
            }

            // Parses the PDDL domain and problem description
            try {
                PDDLParser parser = new PDDLParser();
                ParsedProblem problemParsed = parser.parse(new File(currentDomain), new File(currentProblem));
                ErrorManager errorManager = parser.getErrorManager();
                if (!errorManager.getMessages(Message.Type.PARSER_ERROR).isEmpty()
                        || !errorManager.getMessages(Message.Type.LEXICAL_ERROR).isEmpty()) {
                    errorManager.printAll();
                }

                Assert.assertTrue(errorManager.getMessages(Message.Type.LEXICAL_ERROR).isEmpty()
                    && errorManager.getMessages(Message.Type.PARSER_ERROR).isEmpty());

                try {
                    // Encodes and instantiates the problem in a compact representation
                    System.out.println(" * Instantiation [" + currentProblem + "]" + "...");
                    Problem pb;
                    String typeOfProblem;
                    if (problemParsed.getRequirements().contains(PDDLRequireKey.HIERARCHY)) {
                        pb = new HTNProblem(problemParsed);
                        typeOfProblem = "HTN";
                    } else if (problemParsed.getRequirements().contains(PDDLRequireKey.DURATIVE_ACTIONS)) {
                        pb = new SimpleTemporalProblem(problemParsed);
                        typeOfProblem = "Temporal";
                    } else if (!problemParsed.getRequirements().contains(PDDLRequireKey.DURATIVE_ACTIONS)
                            && problemParsed.getRequirements().contains(PDDLRequireKey.NUMERIC_FLUENTS)) {

                        pb = new NumericProblem(problemParsed);
                        typeOfProblem = "Numeric";
                    } else {
                        pb = new ADLProblem(problemParsed);
                        typeOfProblem = "ADL";
                    }
                    pb.instantiate();
                    Assert.assertTrue(pb != null);
                    if (pb.isSolvable()) {
                        System.out.println(" * "  + typeOfProblem + " problem instantiated (" + pb.getActions().size()
                            + " actions, " + pb.getFluents().size() + " fluents) is solvable.");
                    } else {
                        System.out.println(" * "  + typeOfProblem + " problem instantiated (" + pb.getActions().size()
                            + " actions, " + pb.getFluents().size() + " fluents) is not solvable.");
                    }
                } catch (OutOfMemoryError err) {
                    System.err.println("ERR: " + err.getMessage() + " - test aborted");
                    return;
                } catch (Throwable t) {
                    t.printStackTrace();
                }
            } catch (IOException ioEx) {
                ioEx.printStackTrace();
            }
        }
    }

    /**
     * Instantiate the PDDLParser and parse all domains and problems in the specified test path.
     *
     * @param currentTestPath the path where try to find domain and problems pddl files
     * @param extension the file extension .pddl or .hddl
     * @return all issues report as a ArrayList of String
     * @throws Exception if something wrong.
     */
    public static List<String> parse(String currentTestPath, String extension) throws Exception {

        if (!Tools.isBenchmarkExist(currentTestPath)) {
            System.out.println("missing benchmark directory + \"" + currentTestPath + "\" test skipped !");
            return null;
        }

        final PDDLParser parser = new PDDLParser();
        final ArrayList<String> errors = new ArrayList<>();
        String currentDomain = currentTestPath + "domain" + extension;
        boolean oneDomainPerProblem = false;
        String problemFile;
        String currentProblem;

        // Counting the number of problem files
        File[] pbFileList = new File(currentTestPath)
            .listFiles((dir, name) -> name.startsWith("p") && name.endsWith(extension) && !name.contains("dom"));

        int nbTest = 0;
        if (pbFileList != null) {
            nbTest = pbFileList.length;
        }

        // Check if there is on domain per problem or a shared domain for all
        if (!new File(currentDomain).exists()) {
            oneDomainPerProblem = true;
        }

        System.out.println("\nParser test: Test parser on " + currentTestPath);
        // Loop around problems in one category
        int fillLength = Math.max(Integer.toString(nbTest).length(), 2);
        for (int i = 1; i < nbTest + 1; i++) {
            problemFile = String.format("p%0" + fillLength + "d" + extension, i);
            currentProblem = currentTestPath + problemFile;
            if (oneDomainPerProblem) {
                currentDomain = currentTestPath + problemFile.split(".p")[0] + "-domain" + extension;
            }
            try {
                parser.parse(currentDomain, currentProblem);
                ErrorManager errManager = parser.getErrorManager();
                if (!parser.getErrorManager().getMessages(Message.Type.PARSER_ERROR).isEmpty()
                        || !parser.getErrorManager().getMessages(Message.Type.LEXICAL_ERROR).isEmpty()) {
                    Set<Message> domainMessages = errManager.getMessages(new File(currentDomain));
                    Set<Message> problemMessages = errManager.getMessages(new File(currentProblem));
                    final StringBuilder builder = new StringBuilder();
                    domainMessages.forEach(dMsg -> builder.append(dMsg.toString()));
                    problemMessages.forEach(pMsg -> builder.append(pMsg.toString()));
                    System.out.println("Parser test: [FAILURE]");
                    System.out.println("   * " + currentProblem);
                    System.out.println("   * " + currentDomain);
                    System.out.println("   * Errors:");
                    System.out.println(builder.toString());
                    throw new Exception(builder.toString());
                } else {
                    System.out.println("Parser test: [PASSED]");
                    System.out.println("   * " + currentProblem);
                    System.out.println("   * " + currentDomain);
                    if (!parser.getErrorManager().getMessages(Message.Type.PARSER_WARNING).isEmpty()) {
                        Set<Message> domainMessages = errManager.getMessages(new File(currentDomain));
                        Set<Message> problemMessages = errManager.getMessages(new File(currentProblem));
                        final StringBuilder builder = new StringBuilder();
                        domainMessages.forEach(dMsg -> builder.append(dMsg.toString()));
                        problemMessages.forEach(pMsg -> builder.append(pMsg.toString()));
                        System.out.println("   * Warnings:");
                        System.out.println(builder.toString());
                    }
                }
            } catch (FileNotFoundException fnfException) {
                System.err.println("Test files not found !");
                System.err.println("  -- " + currentDomain);
                System.err.println("  -- " + currentProblem);
                System.err.println("Parser test aborted !");
            }
        }
        return errors;
    }

    /**
     * Check if the OS is Windows.
     *
     * @return true if the OS is Windows, false otherwise.
     */
    private static boolean isWindows() {
        return System.getProperty("os.name").toLowerCase(new Locale("en", "EN")).contains("win");
    }

    /**
     * Check if the OS is Mac.
     *
     * @return true if the OS is Mac, false otherwise.
     */
    private static boolean isMac() {
        return System.getProperty("os.name").toLowerCase(new Locale("en", "EN")).contains("mac");
    }

    /**
     * Check if the OS is Linux.
     *
     * @return true if the OS is Linux, false otherwise.
     */
    private static boolean isUnix() {
        return System.getProperty("os.name").toLowerCase(new Locale("en", "EN")).contains("nux");
    }
}
