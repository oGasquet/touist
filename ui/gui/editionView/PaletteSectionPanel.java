/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gui.editionView;

import gui.editionView.InsertionButton;
import java.awt.GridLayout;
import java.util.ArrayList;
import java.util.List;
import javax.swing.BoxLayout;

/**
 *
 * @author Skander
 */
public class PaletteSectionPanel extends javax.swing.JPanel {

    private List<InsertionButton> buttons;
    private boolean isFold;
    
    /**
     * Creates new form NewPaletteSectionPanel
     */
    public PaletteSectionPanel() {
        initComponents();
        jLabelName.setText("");
        buttons = new ArrayList<>();
        isFold = true;
    }
    
    /**
     * Creates new form NewPaletteSectionPanel
     * @param name section name.
     */
    public PaletteSectionPanel(String name) {
        initComponents();
        jLabelName.setText(name);
        buttons = new ArrayList<>();
        isFold = true;
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabelName = new javax.swing.JLabel();
        jButtonFold = new javax.swing.JButton();
        jPanelsContent = new javax.swing.JPanel();

        setBorder(javax.swing.BorderFactory.createEtchedBorder());

        jLabelName.setFont(new java.awt.Font("Tahoma", 1, 11)); // NOI18N
        jLabelName.setText("<Section name>");

        jButtonFold.setText(">");
        jButtonFold.setFocusable(false);
        jButtonFold.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jButtonFoldActionPerformed(evt);
            }
        });

        jPanelsContent.setLayout(new java.awt.GridLayout(1, 0));

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(jPanelsContent, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
            .addGroup(layout.createSequentialGroup()
                .addComponent(jLabelName)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jButtonFold))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(jLabelName)
                    .addComponent(jButtonFold))
                .addGap(10, 10, 10)
                .addComponent(jPanelsContent, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void jButtonFoldActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jButtonFoldActionPerformed
        isFold = !isFold;
        if (isFold) {
            jButtonFold.setText(">");
            jPanelsContent.removeAll();
        } else {
            jButtonFold.setText("V");
            jPanelsContent.setLayout(new BoxLayout(jPanelsContent, BoxLayout.Y_AXIS));
            for (InsertionButton button : buttons) {
                jPanelsContent.add(button);
            }
        }
    }//GEN-LAST:event_jButtonFoldActionPerformed

public void addInsertButton(InsertionButton button) {
    buttons.add(button);
    updateUI();
}


    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton jButtonFold;
    private javax.swing.JLabel jLabelName;
    private javax.swing.JPanel jPanelsContent;
    // End of variables declaration//GEN-END:variables
}
