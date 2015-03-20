/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gui.editionView;

import gui.editionView.editor.Editor;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.util.ArrayList;
import java.util.List;
import javax.swing.BoxLayout;

/**
 *
 * @author Skander
 */
public class PalettePanel extends javax.swing.JPanel {

    public static enum PaletteType {FORMULA, SET};
    
    private Editor editorTextArea;
    private List<PaletteSectionPanel> sections = new ArrayList<PaletteSectionPanel>();
    
    public PalettePanel() {
        initComponents();
    }
    
    /**
     * Creates new form PalettePanel
     * @param editorTextArea
     */
    public PalettePanel(Editor editorTextArea) {
        initComponents();
        this.editorTextArea = editorTextArea;
    }

    public void setEditorTextArea(Editor editorTextArea) {
        this.editorTextArea = editorTextArea;
    }
    
    public void initPaletteContent(PaletteType type) {
        if (type == PaletteType.FORMULA) {
            PaletteSectionPanel section1 = new PaletteSectionPanel("Section 1");
            PaletteSectionPanel section2 = new PaletteSectionPanel("Section 2");
            sections.add(section1);
            sections.add(section2);

            section1.addInsertButton(new InsertionButton(editorTextArea, "$a and $b", "and"));
            section1.addInsertButton(new InsertionButton(editorTextArea, "$a or $b", "or"));
            section1.addInsertButton(new InsertionButton(editorTextArea, "not $a", "not"));
            section2.addInsertButton(new InsertionButton(editorTextArea, "if $a \nthen \n\t$b \nelse \n\t$c\n", "if then else"));
            section1.addInsertButton(new InsertionButton(editorTextArea, "bigand $i in $a: \n\tA($i) and B($i) \nend", "bigand"));

            sectionsContainerPanel.setLayout(new BoxLayout(sectionsContainerPanel, BoxLayout.Y_AXIS));
            for(PaletteSectionPanel section : sections) {
                sectionsContainerPanel.add(section);
            }
        } else if (type == PaletteType.SET) {
            PaletteSectionPanel section1 = new PaletteSectionPanel("Section 3");
            sections.add(section1);

            section1.addInsertButton(new InsertionButton(editorTextArea, "$a = [a,b,c]", ""));
            section1.addInsertButton(new InsertionButton(editorTextArea, "$b = [a,d,e,f]", ""));

            sectionsContainerPanel.setLayout(new BoxLayout(sectionsContainerPanel, BoxLayout.Y_AXIS));
            for(PaletteSectionPanel section : sections) {
                sectionsContainerPanel.add(section);
            }            
        }
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabel1 = new javax.swing.JLabel();
        sectionsContainerPanel = new javax.swing.JPanel();

        jLabel1.setFont(new java.awt.Font("Tahoma", 1, 11)); // NOI18N
        jLabel1.setText("Insérer");

        sectionsContainerPanel.setLayout(new javax.swing.BoxLayout(sectionsContainerPanel, javax.swing.BoxLayout.LINE_AXIS));

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(sectionsContainerPanel, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
            .addComponent(jLabel1)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(sectionsContainerPanel, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
    }// </editor-fold>//GEN-END:initComponents


    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel jLabel1;
    private javax.swing.JPanel sectionsContainerPanel;
    // End of variables declaration//GEN-END:variables
}