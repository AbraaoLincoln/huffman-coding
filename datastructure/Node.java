package datastructure;

import java.util.HashMap;
import java.util.Map;

public class Node {
    private /*@ spec_public @*/ int letter;
    private /*@ spec_public @*/ int count;
    private /*@ spec_public @*/ Node left;
    private /*@ spec_public @*/ Node right;
    
    //@ public invariant count >=0;

    /*@ assignable this.letter;
     @  ensures this.letter == letter; 
     @*/
    public Node(int letter) {
        this.letter = letter;
    }
    
    /*@
     @ requires left != null && right != right;
     @ assignable this.letter, this.left, this.right;
     @ ensures this.letter == -1;
     @ ensures this.left == left;
     @ ensures this.right == right;
     @*/
    public Node(Node left, Node right) {
        this.letter = -1;
        this.left = left;
        this.right = right;
    }

    public /*@ pure @*/ boolean isLeaf() {
        return this.left == null && this.right == null;
    }
    
    /*
     * requires this.isLeaf() == true || this.letter == -10 || (this.left != null && this.right != null);
     * ensures \old(this.isLeaf()) == true ==> \result == this.count;
     * ensures \old(this.letter) == -10 ==> \result == 1;
     * ensures \old(this.left) != null && \old(this.right) != null) ==> (\result == this.left.getFrequency() + this.right.getFrequency());
     */
    
    /*@
     @   requires this.isLeaf() == true;
     @   ensures  \result == this.count;
     @ also
     @   requires this.letter == -10;
     @   ensures \result == 1;
     @ also
     @   requires this.left != null && this.right != null;
     @   ensures \result == this.left.getFrequency() + this.right.getFrequency();
     @*/
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
     @ assignable count;
     @ ensures count == \old(count) + 1;
     @*/
    public void add() {
        this.count += 1;
    }
    
    /*@  requires codeMap != null && edge != null && this.isLeaf() == true;
     @   ensures codeMap.get(\old((char) this.getLetter())).equals(edge);
     @ also
     @   requires codeMap != null && edge != null && this.isLeaf() == false;
     @
     @*/
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
    
    public static void main(String[] args) {
    	//Node n = new Node(26);
    	//System.out.println(n);
    	
    	Node nl = new Node(27);
    	Node nr = new Node(26);
    	nl.add();
    	nr.add();
    	Node n = new Node(null, null);
    	//n.add();
    	System.out.println(n.isLeaf());
    	//Map<Character, String> codeMap = new HashMap<>();
    	//String e = "0";
    	//n.fillCodingTable(codeMap, e);
    	System.out.println(n.getFrequency());
    	//Node n2 = new Node(9);
    	//System.out.println(n2.getFrequency());
    }
}


