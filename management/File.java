package management;

import java.io.*;
import java.nio.charset.StandardCharsets;

public class File {
    private /*@ spec_public @*/ long size;
    private /*@ spec_public @*/ String text;
    
    //@ public invariant size >= 0;
    
    /*@ requires size >= 0;
     @  assignable this.size;
     @  ensures this.size == size;
     @*/
    public File(long size) {
        this.size = size;
    }
    
    /*@ requires size >= 0;
     @  requires text != null;
     @  assignable this.size, this.text;
     @  ensures this.size == size;
     @  ensures this.text == text;
     @*/
    public File(long size, String text) {
        this.size = size;
        this.text = text;
    }
    
    /*@ requires this.size >= 0;
    @  ensures \result == this.size;
    @*/
    public /*@ pure @*/ long getSize() {
        return size;
    }
    
    /*@ requires this.text != null;
     @  ensures \result.equals(this.text);
     @*/
    public /*@ pure @*/ String getText() {
        return text;
    }
    
    /*@ requires pathname != null;
     @  ensures_redundantly \result.getSize() >= 0;
     @  ensures_redundantly \result.getText() != null;  
     @*/
    public static File read(String pathname) {
        java.io.File file = new java.io.File(pathname);
        BufferedReader fis = null;
        String text = "";
        try {
            Reader reader = new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8);
            fis = new BufferedReader(reader);

            int content;
            while ((content = fis.read()) != -1) {
                if ((int) content < 256) {
                    text += (char) content;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (fis != null)
                    fis.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }

        return new File(file.length(), text);
    }
    
    /*@ requires pathname != null;
     @  ensures_redundantly \result.getSize() >= 0;
     @  ensures_redundantly \result.getText() != null;
     @  ensures (\forall int i; \result.getSize() > 0 && 0 <= i && i < \result.getText().length(); \result.getText().charAt(i) == '0' || \result.getText().charAt(i) == '1');  
     @*/
    public static File readByte(String pathname) {
        java.io.File file = new java.io.File(pathname);
        FileInputStream in = null;
        String text = "";
        try {
            //in = new FileInputStream(pathname);
            //byte[] bytes = in.readAllBytes();
        	byte[] bytes = new byte[(int) file.length()];
        	DataInputStream dataInputStream = new DataInputStream(new FileInputStream(pathname));
        	dataInputStream .readFully(bytes);

            StringBuilder sb = new StringBuilder();
            int i = 0;
            for (; i < Byte.SIZE * bytes.length; i++) {
                sb.append(((bytes[i / Byte.SIZE] & (1 << (i % Byte.SIZE))) != 0) ? '1' : '0');
            }

            text = sb.toString();
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (in != null)
                    in.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
        
        //String t = "10001100";
        return new File(file.length(), text);
    }
    
    /*@ requires pathname != null;
     @  ensures_redundantly \result.getSize() >= 0;
     @  ensures_redundantly \result.getText() != null;  
     @*/
    public static File readExtract(String pathname) {
        java.io.File file = new java.io.File(pathname);
        BufferedReader fis = null;
        String text = "";
        try {
            Reader reader = new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8);
            fis = new BufferedReader(reader);

            int content;
            while ((content = fis.read()) != -1) {
                text += (char) content;
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (fis != null)
                    fis.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }

        return new File(file.length(), text);
    }
    
    /*@ requires pathname != null;
     @  requires content != null;
     @  ensures_redundantly \result.getSize() >= 0;  
     @*/
    public static File write(String pathname, byte[] content) {
        java.io.File file = new java.io.File(pathname);
        FileOutputStream fos = null;

        try {
            fos = new FileOutputStream(file);
            fos.write(content);
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (fos != null)
                    fos.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }

        return new File(file.length());
    }
    
    public static void main(String[] args) {
//		File f = read("/home/abraao/Documentos/java/logica/log");
//    	File f = readByte("/home/abraao/Documentos/java/logica/log");
//    	File f = readExtract("/home/abraao/Documentos/java/logica/log");
//		System.out.println(f.getSize());
//		System.out.println(f.getText().equals(null));
//		System.out.println(f.getText());
//		System.out.println(f.getText().length());
    	//Teste
    	
    	//File f = new File(-1);
    	//File f = new File(10, "/asdas/dasda");
    	
    	//File f = new File(10);
    	//System.out.println(f.getSize());
    	
    	//File f = new File(6, "teste");
    	//System.out.println(f.getText());
    	
    	//File f = read("/home/abraao/Documentos/java/logica/log");
		//System.out.println(f.getSize());
		//System.out.println(f.getText().equals(null));
    	
    	//File f = readByte("/home/abraao/Documentos/java/logica/log");
		//System.out.println(f.getSize());
		//System.out.println(f.getText().length());
		//System.out.println(f.getText().equals(null));
		//System.out.println(f.getText());
		
	}
}
