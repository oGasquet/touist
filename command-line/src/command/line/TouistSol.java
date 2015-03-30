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
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Iterator;
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
        
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
        System.out.println("* Usage: TouistSol [Options...] filename                                    *");
        System.out.println("* General options:                                                          *");
        System.out.println("*  --cnf          read & resolve CNF problem in DIMACS format               *");
        System.out.println("*  --s            read & resolve TouIST problem in TOUISTL format           *");
        System.out.println("*  --t            read TouIST problem in TOUISTL format and build           *");
        System.out.println("*                 (DIMACS format, Hash CNF table)                           *");
        System.out.println("*  -o filename,--output filename                                            *\n"
                +          "*                 write solution to filename in printable format            *");
        
        
        
        System.out.println("*  -h, --help     display this help information and exit                    *");
        System.out.println("*  -v, --version  display program version and exit                          *");
        System.out.println("*                                                                           *");
        System.out.println("*  -v, --version  display program version and exit                          *");
        System.out.println("* TouISTSOL v1.0,2015. Easily formalize and solve real-world sized problems *\n" +
                           "* using propositional logic and linear theory of reals                      *");
        System.out.println("* See TouIST web page at : www.irit.fr/softwave/.../touIST.html             *");
        System.out.println("*                                                                           *");
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
    }
    public static void version(){
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
        System.out.println("* TouISTSOL: TouIST Propositional logic/Linear Theory of reals Solver, v1.0   *\n"
                         + "*                                                                             *\n" +
                           "* Copyright (C) 2015. Toulouse Institute of Computer Science Research,France. *\n" +
                           "* All rights reserved.Email:<.....@irit.fr>                                   *\n"+
                           "* Contributors:                                                               *\n" +
                           "*     Khaled Skander Ben Slimane, Alexis Comte, Olivier Gasquet,              *\n" +
                           "*     Abdelwahab Heba, Olivier Lezaud, Frédéric Maris, Maël Valais            *\n"
                        +  "*                                                                             *");
        
        System.out.println("* This program is free software; you may re-distrubute it under the terme of  *\n"+
                           "* the GNU Lesser General Public License (LGPL) version 2.1 which accompanies  *\n"
                         + "* this distribution, and is available at :                                    *\n"
                         + "* http://www.gnu.org/licenses/lgpl-2.1.html                                   *");
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
    }
    public static void empty(String arg,int number){
    if(number==1){
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("No input option; try TouISTSol --help                             ");
    }
    else{
        if(number==2)
        {
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("Invalid option '"+arg+"'; try TouISTSol --help                             ");   
        }
        if(number==3)
        {
    System.out.println("TouISTSOL v1.0,2015.");
    System.out.println("Parameter(s) specified in the command line:\n "+arg);
    System.out.println("No input problem file specified; try TouISTSol --help                             ");
        }
        if(number==4){
         System.out.println("No output solution file specified");
        }
    }
    }
    public static void solvetouISTL(String path,int nb) throws IOException, InterruptedException{
        Translator translator = new Translator("compiler"+File.separatorChar+"touistc.native");
        if(translator.translate(path))
        {
            Minisat solver= new Minisat(translator.getDimacsFilePath(),nb,translator.getLiteralsMap());
            Models m=solver.resolveTouISTLProblem();
            for (Model m1: m.getModels()){
                System.out.println(m1.toString());
            }
        }
    }
    
    public static void solveCNF(String path,int nb,int control,String pathSave) throws FileNotFoundException, IOException{
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
        StringBuilder str=new StringBuilder();
        for (Model m1: m.getModels()){
                str.append(m1.toString()+"\n");
            }
        if(control==1)
            System.out.println(str.toString());
        else
           Output(pathSave,str.toString());
    }
    public static void translate(String path) throws IOException, InterruptedException{
        Translator translator = new Translator("compiler"+File.separatorChar+"touistc.native");
        if(translator.translate(path))
        {
         System.out.println("CNF FILE :"+translator.getDimacsFilePath());
         System.out.println("<Key,Literal>: \n");
          while(translator.getLiteralsMap().entrySet().iterator().hasNext()){
              Map.Entry<Integer, String> e= translator.getLiteralsMap().entrySet().iterator().next();
              System.out.println(e.getKey()+" "+e.getValue());
          }
        }
    }
    
    public static void Output(String nameFile,String out) throws IOException{
        BufferedWriter wr=new BufferedWriter(new FileWriter(nameFile));
        wr.write(out);
        wr.flush();
        wr.close();
    }
    public static void main(String[] args) throws IOException, InterruptedException {
        /* 
         * TODO code application logic here
         */
        String a[]={"--cnf","term1_gr_2pin_w4.shuffled.cnf","1","-o"};
         String path="";
         File f;
            switch(a[0]){
                //General Option
                case "--help": help();System.exit(0);
                case "-h": help();System.exit(0);
                case "--version": version();System.exit(0);
                case "-v": version();System.exit(0);
                //Solver Option SAT:
                //Using TouIST Language
                case "--t":   
                    path=CurrentPath+File.separatorChar+a[1];
                    f=new File(path);
                    if(f.isFile() && path.endsWith(".touistl"))
                        translate(path);
                    System.exit(0);
                case "--s": if(a.length==3){ 
                    path=CurrentPath+File.separatorChar+a[1];
                    f=new File(path);
                    if(f.isFile() && path.endsWith(".touistl"))
                    solvetouISTL(CurrentPath+File.separatorChar+a[1],Integer.parseInt(a[2]));
                    else
                       System.out.println("le fichier doit etre d'extension .touisl");
                    }
                    else empty(a[0],3);System.exit(0);
               //Using CNF format
                case "--cnf":  
                    if( a.length==3 || a.length==5){
                         path=CurrentPath+File.separatorChar+a[1];
                          f=new File(path);
                            if(f.isFile() && path.endsWith(".cnf"))
                            {  if(a.length==3)
                                 solveCNF(CurrentPath+File.separatorChar+a[1],Integer.parseInt(a[2]),1,null);
                                else
                                 solveCNF(CurrentPath+File.separatorChar+a[1],Integer.parseInt(a[2]),0,CurrentPath+File.separatorChar+a[4]);
                            }else
                                 System.out.println("le fichier doit etre d'extension .cnf");
                    }else{
                        //System.out.println("eo"+a.length);
                        if(a.length==4)
                        {if(a[3].equals("-o") || a[3].equals("--output"))
                                empty(null,4);
                            else
                            empty(a[3],3);}            
                    }
                      System.exit(0);
                //Solver Option SMT
                case "--smt":
                            System.exit(0);
                default: if(a.length==0) empty(null,1);else empty(a[0],2);System.exit(0);
            }
       
    }
}
