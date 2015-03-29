/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package Solver.SAT;
/*
 *
 * Project TouIST, 2015. Easily formalize and solve real-world sized problems
 * using propositional logic and linear theory of reals with a nice GUI.
 *
 * https://github.com/olzd/touist
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser General Public License
 * (LGPL) version 2.1 which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/lgpl-2.1.html
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * Contributors:
 *     Alexis Comte, Abdelwahab Heba, Olivier Lezaud,
 *     Skander Ben Slimane, Maël Valais
 *
 */
/**
 *
 * @author Abdel
 */
import Solver.SAT.Entity.Literal;
import Solver.SAT.Entity.Models;
import Solver.SAT.Entity.Model;
import java.io.FileNotFoundException;
import java.io.IOException;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import java.util.Map;
import org.sat4j.tools.ModelIterator;


public class Minisat {
    private ISolver solver;
    private ModelIterator mi;
    private DimacsReader dimacs_reader;
    private IProblem problem;
    //private BufferedReader _buffreader;
    private int nb_model;
    private String cnf_path;
    private Map<Integer,String> LiteralsMap;
   public Minisat(String cnf_path,int nb_model,Map<Integer,String> LiteralMap){
       dimacs_reader=init_Solver();
       this.LiteralsMap=LiteralMap;
       this.nb_model=nb_model;
       this.cnf_path=cnf_path;
   }
   public Minisat(String cnf_path,int nb_model){
       dimacs_reader=init_Solver();
       this.nb_model=nb_model;
       this.cnf_path=cnf_path;
   }
   public Minisat(String cnf_path){
       dimacs_reader=init_Solver();
       this.cnf_path=cnf_path;
   }
   private DimacsReader init_Solver(){
        //Instanciate MiniSat Solver from org.sat4j.minisat.SolverFactory
        this.solver = SolverFactory.newDefault();
        //IteratorModel Reader
        this.mi = new ModelIterator(solver);
        //TimeLimite for executing this Solver session
        solver.setTimeout(3600); // 1 hour timeout
        //DimacsReader will be an Iterator Reader for Solver Instance to resolve Problem
       return new DimacsReader(mi);
   }
   private Model parseModel(String[] model_parse){
        Model model = new Model();
            for (String LiteralIndex : model_parse) {
		int literalInt = Integer.parseInt(LiteralIndex);
			if (literalInt != 0) { // '0' means 'end of model'
				int literalCode = (literalInt > 0 ? literalInt : literalInt * (-1));
				model.addLiteral(new Literal(LiteralsMap.get(literalCode),
                                                                            literalInt > 0));
			}
		}
		return model;
   }
   public Models resolveTouISTLProblem(){
       Models models=new Models(); 
       try {
            //IProblem is an Instance who contain Problem Format(CNF)
            //if File contain wron CNF format, ParseFrmatException will be generated.
            this.problem = dimacs_reader.parseInstance(cnf_path);
            boolean unsat=true;
            // Buffered Input Reader will able to communicate(pipe) with Main Program
            //_buffreader =new BufferedReader(new InputStreamReader(System.in));
            // 1 to Run each model and 0 to exit program.
            while(problem.isSatisfiable() && nb_model!=0) {
                unsat=false;
                //System.out.println("Satisfiable !");
                //problem model return int[] Satisfiable model
                String model="";
                model=dimacs_reader.decode(problem.model());
                String[] model_p=model.split(" ");
                models.addModels(parseModel(model_p));
                nb_model--;
            }
            if(unsat)
                System.out.println("Unsatisfiable !");
            else if(nb_model!=0){
                System.out.println("Limited satisfaction models:"+models.getModels().size());
            }
        
        //Catch Exceptions....
        } catch (FileNotFoundException e) {
            System.out.println("Error Loading File");
           System.exit(2);
        } catch (ParseFormatException e) {
            System.out.println("Incorrect Dimacs Content");
            System.exit(3);
        } catch (IOException e) {
            System.out.println("Error StreamReader");
            System.exit(4);
        } catch (ContradictionException e) {
            System.out.println("Unsatisfiable (trivial)!");
            System.exit(1);
        }catch (org.sat4j.specs.TimeoutException ex) {
            System.out.println("Timeout Solver/Please Restart");
            System.exit(6);
        }
       return models;
   }
   public StringBuffer resolveCNFProblem(){
       StringBuffer br=new StringBuffer();
       try {
            //IProblem is an Instance who contain Problem Format(CNF)
            //if File contain wron CNF format, ParseFrmatException will be generated.
            this.problem = dimacs_reader.parseInstance(cnf_path);
            boolean unsat=true;
            // Buffered Input Reader will able to communicate(pipe) with Main Program
            //_buffreader =new BufferedReader(new InputStreamReader(System.in));
            // 1 to Run each model and 0 to exit program.
            while(problem.isSatisfiable() && nb_model!=0) {
                unsat=false;
                //System.out.println("Satisfiable !");
                //problem model return int[] Satisfiable model
                String model="";
                model=dimacs_reader.decode(problem.model());
                model=model.substring(0, model.length()-2);
                br.append(model+"\n");
                nb_model--;
            }
            if(unsat)
                System.out.println("Unsatisfiable !");
            else if(nb_model!=0){
                System.out.println("Limited satisfaction models:"+br.length());
            }
        //Catch Exceptions....
        } catch (FileNotFoundException e) {
            System.out.println("Error Loading File");
           System.exit(2);
        } catch (ParseFormatException e) {
            System.out.println("Incorrect Dimacs Content");
            System.exit(3);
        } catch (IOException e) {
            System.out.println("Error StreamReader");
            System.exit(4);
        } catch (ContradictionException e) {
            System.out.println("Unsatisfiable (trivial)!");
            System.exit(1);
        }catch (org.sat4j.specs.TimeoutException ex) {
            System.out.println("Timeout Solver/Please Restart");
            System.exit(6);
        }
       return br;
       
   }
}
