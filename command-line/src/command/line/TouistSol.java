/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package command.line;

import Solver.SAT.Entity.Model;
import Solver.SAT.Entity.Models;
import Solver.SAT.Minisat;
import Translator.Translator;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author Abdel
 */
enum Commande{
        help("--help"),
        h("-h"),
        version("--version"),
        v("-v"),
        s("-s");
        String name="";
        Commande(String name){
            this.name=name;   
        }
        public String toString(){
            return name;
            }
    }
public class TouistSol {

    /**
     * @param args[0] the command line arguments --help
     * @param args[1] the commande li
     * 
     * 
     * 
     */
    private static String CurrentPath=Paths.get("").toAbsolutePath().toString();
    
    public static void help(){
        
        System.out.println("***************************************************************************");
        
        
        
        
        
        
        
        
        
        System.out.println("*TouISTSOL v1.0,2015. Easily formalize and solve real-world sized problems*\n" +
                           "*using propositional logic and linear theory of reals                     *");
        System.out.println("*See TouIST Language on : www.irit.fr/~sdqsd/grammar.pdf                  *");
        System.out.println("*No input problem file specified; try TouISTSol --help                    *");
        System.out.println("***************************************************************************");
    }
    public static void version(){
        System.out.println("***************************************************************************");
        
        System.out.println("*TouISTSOL: TouIST Propositional logic/Linear Theory of reals Solver, v1.0  *\n"
                         + "*                                                                           *\n" +
                           "*Copyright (C) 2015. Toulouse Institute of Computer Science Research,France.*\n" +
                           "*All rights reserved.Email:<.....@irit.fr>                                  *\n"+
                           "*Contributors:                                                              *\n" +
                           "*     Khaled Skander Ben Slimane, Alexis Comte, Olivier Gasquet,            *\n" +
                           "*     Abdelwahab Heba, Olivier Lezaud, Frédéric Maris, Maël Valais          *\n"
                        +  "*                                                                           *");
        
        System.out.println("*This program is free software; you may re-distrubute it under the terme of *\n"+
                           "*the GNU Lesser General Public License (LGPL) version 2.1 which accompanies *\n"
                         + "*this distribution, and is available at :                                   *\n"
                         + "*http://www.gnu.org/licenses/lgpl-2.1.html                                  *"
                        );
        System.out.println("***************************************************************************");
    }
    public static void empty(String arg,int number){
    if(number==1){
    //System.out.println("************************************************************************************");
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("No input option; try TouISTSol --help                             ");
    //System.out.println("************************************************************************************");
    }
    else{
        if(number==2)
        {
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("Invalid option '"+arg+"'; try TouISTSol --help                             ");   
        }
        if(number==3)
        {
    //System.out.println("************************************************************************************");
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("Parameter(s) specified in the command line:\n "+arg);
    System.out.println("No input problem file specified; try TouISTSol --help                             ");
    //System.out.println("************************************************************************************");  
        }
        if(number==4){
            
        }
    }
    }
    public static void solvetouISTL(String path) throws IOException, InterruptedException{
        Translator translator = new Translator("compiler"+File.separatorChar+"touistc.native");
        if(translator.translate(path))
        {
            Minisat solver= new Minisat(translator.getDimacsFilePath(),5,translator.getLiteralsMap());
            Models m=solver.resolveTouISTLProblem();
            for (Model m1: m.getModels()){
                System.out.println(m1.toString());
            }
        }
    }
    
    public static void solveCNF(String path,int nb) throws FileNotFoundException, IOException{
        Map<Integer,String> mp=new HashMap<Integer,String>();
        File f=new File(path);
        BufferedReader br=new BufferedReader(new FileReader(f));
        String line="";
        br.readLine();
        br.readLine();
        while((line=br.readLine())!=null){
            String[] line1=line.split(" ");
            for (String line2:line1)
            {
                int number=Integer.parseInt(line2);
                number=(number>0? number:number*(-1));
                if(number!=0 && !mp.containsKey(number))
                    mp.put(number,"P("+number+")");
            }
        }
        
        Minisat solver=new Minisat(path,nb,mp);
        
        Models m=solver.resolveTouISTLProblem();
        //System.out.print("Modele:{");
            for (Model m1: m.getModels()){
                System.out.print(m1.toString());
            }
       //System.out.println("");
        // Minisat solver1=new Minisat(path,nb);
        //StringBuffer br1=solver1.resolveCNFProblem();
        //String[] br2=br1.toString().split("\n");
         //  for (String m1: br2){
          //      System.out.println(m1.toString());
           // }
        
    }
    public static void main(String[] args) throws IOException, InterruptedException {
        /* 
         * TODO code application logic here
         */
        String a[]={"--cnf","term1_gr_2pin_w4.shuffled.cnf","1"};
            switch(a[0]){
                //General Option
                case "--help": help();System.exit(0);
                case "-h": help();System.exit(0);
                case "--version": version();System.exit(0);
                case "-v": version();System.exit(0);
                //Using TouIST Language
                case "--s": if(a.length==2){ 
                    if(new File(CurrentPath+File.separatorChar+a[1]).isDirectory())
                    solvetouISTL(CurrentPath+File.separatorChar+a[1]);
                    else
                    {
                       System.out.println("test_reussi");
                    }
                    }
                    else empty(a[0],3);System.exit(0);
               //Using CNF format
                case "--cnf": if(a.length==3){
                            //File f=new File(CurrentPath+File.separatorChar+a[1]);    
                            //if(f.isDirectory())
                                    solveCNF(CurrentPath+File.separatorChar+a[1],Integer.parseInt(a[2]));
                              //  else
                                //    System.out.println("not file");
                            }
                              else
                                if(a.length==2)
                               System.exit(0);
                case "--smt":
                            System.exit(0);
                default: if(a.length==0) empty(null,1);else empty(a[0],2);System.exit(0);
            }
       
    }
}
