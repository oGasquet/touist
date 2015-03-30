/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package Solver.SAT.Entity;

import Solver.SAT.Entity.Literal;
import java.util.ArrayList;

/**
 *
 * @author WAHAB
 */
public class Model {
    private ArrayList<Literal> literals;
    public Model(){
        literals=new ArrayList<Literal>();
    }
    public ArrayList<Literal> getLiterals() {
        return literals;
    }

    public void addLiteral(Literal literal) {
        this.literals.add(literal);
    }
    public String toString() {
		// TODO Please write a proper toString
		String out = "Modele (Literals Valuated=True):\n {";
		for (Literal s : literals) {
                   // out = out + " " + s.getLiteral()+ " Valuated : "+s.isLiteral_positivity()+"\n";
                    if(s.isLiteral_positivity())
			out = out +s.getLiteral()+"; ";
		}
                
		return out.subSequence(0, out.length()-2)+"}";
	}
}
