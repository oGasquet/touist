/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package Solver.SAT.Entity;

import Solver.SAT.Entity.Model;
import java.util.ArrayList;

/**
 *
 * @author WAHAB
 */
public class Models {
    private ArrayList<Model> models;
    public Models(){
        models=new ArrayList<Model>();
    }

    public ArrayList<Model> getModels() {
        return models;
    }

    public void addModels(Model model) {
        this.models.add(model);
    }
}
