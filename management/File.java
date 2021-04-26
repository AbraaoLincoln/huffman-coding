package management;

import java.io.*;
import java.nio.charset.StandardCharsets;

public class File {
    private /*@ public_spec*/ long size;
    private /*@ public_spec*/ String text;
    
    //@ public invariant size >= 0;
    //@ public invariant text != null;
    
    /*@ requires size >= 0;
     *@ assignable size;
     *@ ensures this.size == size;
     * */
    public File(long size) {
        this.size = size;
    }
    
    /*@ requires size >= 0;
     *@ requires text != null;
     *@ assignable size, text;
     *@ ensures this.size == size;
     *@ ensures this.text == text;
     * */
    public File(long size, String text) {
        this.size = size;
        this.text = text;
    }
    
    /*@ requires this.size >= 0;
     *@ ensures \result == this.size;
     * */
    public /*@ pure @*/ long getSize() {
        return size;
    }
    
    /*@ requires this.text != null;
     *@ ensures \result == this.text;
     * */
    public /*@ pure @*/ String getText() {
        return text;
    }
    
    /*@ requires pathname != null;
     *@ ensures \result.getSize() >= 0;
     *@ ensures \result.getText() != null;  
     * */
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
     *@ ensures \result.getSize() >= 0;
     *@ ensures \result.getText() != null;  
     *@ ensures (\forall int i; \result.getSize() > 0 && (0 <= i < \result.getText().length()); 	  \result.getText().charAt(i) == 0 || \result.getText().charAt(i) == 1);  
     * */
    public static File readByte(String pathname) {
        java.io.File file = new java.io.File(pathname);
        FileInputStream in = null;
        String text = "";
        try {
            in = new FileInputStream(pathname);
            byte[] bytes = in.readAllBytes();

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

        return new File(file.length(), text);
    }
    
    /*@ requires pathname != null;
     *@ ensures \result.getSize() >= 0;
     *@ ensures \result.getText() != null;  
     * */
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
     *@ requires content != null;
     *@ ensures \result.getSize() >= 0;  
     * */
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
}

