/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gui.editionView;

import entity.Model;
import gui.AbstractComponentPanel;
import gui.Lang;
import gui.MainFrame;
import gui.State;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ListIterator;
import java.util.Map;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import solution.NotSatisfiableException;
import solution.SolverExecutionException;
import solution.SolverTestSAT4J;
import translation.Translator;

/**
 *
 * @author Skander
 */
public class ParentEditionPanel extends AbstractComponentPanel {

    /**
     * Creates new form FormulasPanel
     */
    public ParentEditionPanel() {
        initComponents();
        editorPanelFormulas.initPalette(PalettePanel.PaletteType.FORMULA);
        editorPanelSets.initPalette(PalettePanel.PaletteType.SET);
        jFileChooser1.setCurrentDirectory(new File(".."));
        jLabelErrorMessage.setText("");
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jFileChooser1 = new javax.swing.JFileChooser();
        jOptionPane1 = new javax.swing.JOptionPane();
        jTabbedPane1 = new javax.swing.JTabbedPane();
        editorPanelFormulas = new gui.editionView.EditionPanel();
        editorPanelSets = new gui.editionView.EditionPanel();
        testButton = new javax.swing.JButton();
        importButton = new javax.swing.JButton();
        jLabelErrorMessage = new javax.swing.JLabel();
        jLabelCaretPosition = new javax.swing.JLabel();

        jTabbedPane1.setToolTipText("");
        jTabbedPane1.addTab("Formulas", editorPanelFormulas);
        jTabbedPane1.addTab("Sets", editorPanelSets);

        testButton.setText("Test");
        testButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                testButtonActionPerformed(evt);
            }
        });

        importButton.setText("Import");
        importButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                importButtonActionPerformed(evt);
            }
        });

        jLabelErrorMessage.setForeground(new java.awt.Color(255, 0, 0));
        jLabelErrorMessage.setText("<Error message>");

        jLabelCaretPosition.setText("0:0");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(jTabbedPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 713, Short.MAX_VALUE)
            .addGroup(javax.swing.GroupLayout.Alignment.TRAILING, layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jLabelCaretPosition)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jLabelErrorMessage)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                .addComponent(importButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(testButton)
                .addContainerGap())
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addComponent(jTabbedPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 510, Short.MAX_VALUE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(testButton)
                    .addComponent(importButton)
                    .addComponent(jLabelCaretPosition)
                    .addComponent(jLabelErrorMessage))
                .addContainerGap())
        );
    }// </editor-fold>//GEN-END:initComponents

    private void importButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_importButtonActionPerformed
        switch(((MainFrame)(getRootPane().getParent())).state) {
            case EDITION :
                setState(State.EDITION);
                importHandler();
                break;
            case EDITION_ERROR :
                setState(State.EDITION_ERROR);
                importHandler();
                break;
            case NO_RESULT :
                // impossible
                break;
            case SINGLE_RESULT :
                // impossible
                break;
            case FIRST_RESULT :
                // impossible
                break;
            case MIDDLE_RESULT :
                // impossible
                break;
            case LAST_RESULT :
                // impossible
                break;
            default : 
                System.out.println("Undefined action set for the state : " + getState());
        }
    }//GEN-LAST:event_importButtonActionPerformed

    private void testButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_testButtonActionPerformed
        switch(((MainFrame)(getRootPane().getParent())).state) {
            case EDITION :
                jLabelErrorMessage.setText("");
                State state = initResultView();
                if (state != State.EDITION) {
                    setState(state);
                    getFrame().setViewToResults();
                }
                break;
            case EDITION_ERROR :
                // interdit
                break;
            case NO_RESULT :
                // impossible
                break;
            case SINGLE_RESULT :
                // impossible
                break;
            case FIRST_RESULT :
                // impossible
                break;
            case MIDDLE_RESULT :
                // impossible
                break;
            case LAST_RESULT :
                // impossible
                break;
            default : 
                System.out.println("Undefined action set for the state : " + getState());
        }
    }//GEN-LAST:event_testButtonActionPerformed


    // Variables declaration - do not modify//GEN-BEGIN:variables
    private gui.editionView.EditionPanel editorPanelFormulas;
    private gui.editionView.EditionPanel editorPanelSets;
    private javax.swing.JButton importButton;
    private javax.swing.JFileChooser jFileChooser1;
    private javax.swing.JLabel jLabelCaretPosition;
    private javax.swing.JLabel jLabelErrorMessage;
    private javax.swing.JOptionPane jOptionPane1;
    private javax.swing.JTabbedPane jTabbedPane1;
    private javax.swing.JButton testButton;
    // End of variables declaration//GEN-END:variables

    private void importHandler() {
        String path = "";
        int returnVal;
        getFrame().getClause().setFormules("");
        getFrame().getClause().setSets("");
        
        jFileChooser1.setFileSelectionMode(JFileChooser.FILES_ONLY);
        returnVal = jFileChooser1.showDialog(this, getFrame().getLang().getWord(Lang.EDITION_FILE_CHOOSER));
        
        if (returnVal == JFileChooser.APPROVE_OPTION && jFileChooser1.getSelectedFile() != null) {
            path = jFileChooser1.getSelectedFile().getPath();

            try {
                getFrame().getClause().uploadFile(path);
            } catch(Exception e) {
                //TODO handle error message
                System.out.println("Error : Failed to load the file : " + path);
                e.printStackTrace();
            }

            //Réinitialisation des sets et des formules
            String text = getFrame().getClause().getFormules();
            editorPanelFormulas.setText(text);
            text = getFrame().getClause().getSets();
            editorPanelSets.setText(text);
        }   
    }
    
    private void showErrorMessage(String message, String title) {
        jOptionPane1.showMessageDialog(getParent(), 
                        message, 
                        title, 
                        JOptionPane.ERROR_MESSAGE);
    }
    
    private void showErrorMessage(Exception e, String message, String title) {
        showErrorMessage(message, title);
        FileWriter writer = null;
        String texte = String.valueOf(e.getStackTrace()) + "\n" + "######################";
        try{
             writer = new FileWriter("log.txt", true);
             writer.write(texte,0,texte.length());
        }catch(IOException ex){
            ex.printStackTrace();
        }finally{
          if(writer != null){
              try {
                  writer.close();
              } catch (IOException ex) {
                  e.printStackTrace();
              }
          }
        }
    }
    
    private Translator.Error guiTranslationErrorAdapter(Translator.Error error) {
        Translator t = new Translator("");
        Translator.Error adaptedError;
        int row = error.getRowInCode();
        String sets = getFrame().getClause().getSets();
        int nbRowsInSets = 1;
        int setShift = (getFrame().getClause().getSets().isEmpty()) ? 0 : -1; // -1 pour tenir compte de "begin sets";
        int formulasShift = (getFrame().getClause().getSets().isEmpty()) ? 0 : -3; // -3 pour tenir compte de "begin sets", "end sets" et "begin formulas"
        
        for (int i=0; i<sets.length(); i++) {
            if (sets.charAt(i) == '\n') {
                nbRowsInSets++;
            }
        }
        if (row < nbRowsInSets) {
            // l'erreur est dans les sets
            adaptedError = t.new Error(row - setShift,
                    error.getColumnInCode(), 
                    error.getErrorMessage() + getFrame().getLang().getWord(Lang.ERROR_TRADUCTION_IN_SETS));
        } else {
            // l'erreur est dans les formules
            adaptedError = t.new Error(row-nbRowsInSets - formulasShift, 
                    error.getColumnInCode(), 
                    error.getErrorMessage() + getFrame().getLang().getWord(Lang.ERROR_TRADUCTION_IN_FORMULAS));
        }
        return adaptedError;
    }

    private State initResultView() {
        // Initialisation de BaseDeClause
        getFrame().getClause().setFormules("");
        getFrame().getClause().setFormules("");
        getFrame().getClause().addFormules(editorPanelFormulas.getText());
        getFrame().getClause().addSets(editorPanelSets.getText());
        
        /*
        Faire appel au solveur avec les fichiers générés par le traducteur
        calculer un model
        Si un model suivant existe
        alors passer a l'état FIRST_RESULT
        sinon passer à l'état SINGLE_RESULT
        Si aucun model n'existe alors passer a l'état NO_RESULT
        */
        String bigAndFilePath = "bigAndFile-defaultname.txt"; //TODO se mettre d'accord sur un nom standard ou ajouter a Translator et BaseDeClause des méthode pour s'échange de objets File
        String errorMessage;
        
        
        try {
            getFrame().getClause().saveToFile(bigAndFilePath); //TODO gérer les IOException
        } catch (IOException ex) {
            ex.printStackTrace();
            errorMessage = "Couldn't create file '" + bigAndFilePath + "'";
            showErrorMessage(errorMessage, getFrame().getLang().getWord(Lang.ERROR_TRADUCTION));
            System.exit(0);
            return State.EDITION;
        }
        try {
            if(! getFrame().getTranslator().translate(bigAndFilePath)) {
                errorMessage = "";
                for(int i=0; i<getFrame().getTranslator().getErrors().size(); i++) {
                    Translator.Error error = guiTranslationErrorAdapter(getFrame().getTranslator().getErrors().get(i));
                    errorMessage += (i+1) + ": " + error + "\n";
                }
                jLabelErrorMessage.setText(errorMessage);
                System.out.println("Traduction error : " + "\n" + errorMessage + "\n");
                showErrorMessage(errorMessage, getFrame().getLang().getWord(Lang.ERROR_TRADUCTION));
                return State.EDITION;
            }
            File f = new File(bigAndFilePath);
            f.deleteOnExit();
        } catch (IOException ex) {
            ex.printStackTrace();
            errorMessage = "The translator returned an IOException";
            showErrorMessage(ex, errorMessage, getFrame().getLang().getWord(Lang.ERROR_TRADUCTION));
            return State.EDITION;
        } catch (InterruptedException ex) {
            ex.printStackTrace();
            errorMessage = "Translator has been interrupted.";
            showErrorMessage(ex, errorMessage, getFrame().getLang().getWord(Lang.ERROR_TRADUCTION));
            return State.EDITION;
        }
        
        //Add CurrentPath/dimacsFile
        String translatedFilePath = getFrame().getTranslator().getDimacsFilePath();
        Map<Integer, String> literalsMap = getFrame().getTranslator().getLiteralsMap();
        getFrame().setSolver(new SolverTestSAT4J(translatedFilePath, literalsMap));
        
        try {
            getFrame().getSolver().launch();
        } catch (IOException ex) {
            ex.printStackTrace();
            errorMessage = "Couldn't launch solver.";
            showErrorMessage(ex, errorMessage, "Solver error");
            return State.EDITION;
        }
        if(! getFrame().getSolver().isSatisfiable()) {
            System.out.println("Error : unsatisfiable");
        }        
            
        // Si il y a au moins un model
        try {
            ListIterator<Model> iter = (ListIterator<Model>) getFrame().getSolver().getModelList().iterator();
            getFrame().updateResultsPanelIterator(iter);
            /**
             * Si il y a plus d'un model, alors passer à l'état FIRST_RESULT
             * sinon passer à l'état SINGLE_RESULT
             */
            if (iter.hasNext()) {
                getFrame().setResultView(iter.next());
                if (iter.hasNext()) {
                   //iter.previous();
                    return State.FIRST_RESULT;
                } else {
                    //iter.previous();
                    return State.SINGLE_RESULT;
                }
            } else {
                return State.SINGLE_RESULT;
            }
        } catch (NotSatisfiableException ex) {
            ex.printStackTrace();
            errorMessage = "There is no solution.";
            showErrorMessage(ex, errorMessage, "Solver error");
            return State.EDITION;
        } catch (SolverExecutionException ex) {
            ex.printStackTrace();
            errorMessage = "The solver encountered a problem.";
            showErrorMessage(ex, errorMessage, "Solver error");
            return State.EDITION;
        }
        //return State.NO_RESULT;
    }
    
    public void setJLabelCaretPositionText(String text) {
        jLabelCaretPosition.setText(text);
    }

    @Override
    public void updateLanguage() {
        importButton.setText(getFrame().getLang().getWord(Lang.EDITION_IMPORT));
        testButton.setText(getFrame().getLang().getWord(Lang.EDITION_TEST));
        editorPanelFormulas.updateLanguage();
        editorPanelSets.updateLanguage();
        jTabbedPane1.setTitleAt(0, getFrame().getLang().getWord(Lang.EDITION_TAB_FORMULAS));
        jTabbedPane1.setTitleAt(1, getFrame().getLang().getWord(Lang.EDITION_TAB_SETS));
        updateUI();
    }
}
