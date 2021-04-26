package datastructure;

import java.util.Map;

public class Node {
    private int letter;
    private /*@ spec_public @*/ int count;
    private Node left;
    private Node right;
    
    //@ public invariant count >=0;
    
    /*@ assignable letter;
     *@ ensures this.letter == letter; 
     * */
    public Node(int letter) {
        this.letter = letter;
    }
    
    /*@ requires left != null && right == != null;
     *@ assignable letter, left, right;
     *@ ensures this.letter == -1;
     *@ ensures this.left == left;
     *@ ensures this.right == right; 
     * */
    public Node(Node left, Node right) {
        this.letter = -1;
        this.left = left;
        this.right = right;
    }

    public /*@ pure @*/ boolean isLeaf() {
        return this.left == null && this.right == null;
    }
    
    /*
     *@ requires this.isLeaf() == true || this.letter == -10 || (this.left != null && this.right != null);
     *@ ensures \old(this.isLeaf() == true) ==> (\result == this.count);
     *@ ensures \old(this.letter == -10) ==> (\result == 1);
     *@ ensures \old(this.left != null && this.right != null) ==> (\result == this.left.getFrequency() + this.right.getFrequency());
     * */
    public /*@ pure @*/ int getFrequency() {
        if (this.isLeaf()) {
            return this.count;
        }

        if (this.letter == -10) {
            return 1;
        }

        return this.left.getFrequency() + this.right.getFrequency();
    }

    public /*@ pure @*/ int getLetter() {
        return this.letter;
    }

    public /*@ pure @*/ Node getLeft() {
        return this.left;
    }

    public /*@ pure @*/ Node getRight() {
        return this.right;
    }
    
    /*@ 
     *@ assignable count;
     *@ ensures count = \old(count) + 1;
     * */
    public void add() {
        this.count += 1;
    }
    
    /*@   requires codeMap != null && edge != null && this.isLeaf() == true;
     *@   ensures codeMap.get(\old((char) this.getLetter())).equals(edge);
     *@   ensures (\forall char c; c != \old((char) this.getLetter()) && 
     *@				(codeMap.keySet().contains(new Character(c)));
     *@             codeMap.get(c).equals(\old(codeMap.get(c)));
     *@ also
     *@   requires codeMap != null && edge != null && this.isLeaf() == false;
     *@
     * */
    public void fillCodingTable(Map<Character, String> codeMap, String edge) {
        if (this.isLeaf()) {
            codeMap.put((char) this.getLetter(), edge);
            return;
        }

        this.left.fillCodingTable(codeMap, edge + "0");
        this.right.fillCodingTable(codeMap, edge + "1");
    }

    @Override
    public /*@ pure @*/ String toString() {
        return String.format("'%d': %d", this.getLetter(), this.getFrequency());
    }
}


