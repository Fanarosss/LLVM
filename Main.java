import syntaxtree.*;
import visitor.*;
import java.io.*;
import java.util.*;

public class Main {
    public static void main (String [] args){
        if(args.length < 1){
            System.err.println("Usage: java [MainClassName] [file1] [file2] ... [fileN]");
            System.exit(1);
        }
        FileInputStream fis = null;
        try{
            for (int j = 0; j < args.length; j++){
                fis = new FileInputStream(args[j]);
                MiniJavaParser parser = new MiniJavaParser(fis);
                Goal root = parser.Goal();
                System.out.println("Parsed successfully file: " + args[j]);
                STMap.SymTable Symbol_Table = new STMap.SymTable();
                Stack<STMap.Level> GlobalSymbolTable = new Stack<STMap.Level>();
                /* First visitor */
                ScopeVisitor visitor = new ScopeVisitor(GlobalSymbolTable, Symbol_Table);
                root.accept(visitor, Symbol_Table);
                System.out.println("First visit to check scopes was successful.");
                /* Second visitor */
                TypeCheckerVisitor visitor2 = new TypeCheckerVisitor(Symbol_Table);
                root.accept(visitor2, Symbol_Table);
                System.out.println("Type check visitor finished with success!");
                /* Third visitor */
                String filename = Extract_Filename(args[j]);
                FileOutputStream buff;
                try {
                    buff = new FileOutputStream(filename);
                    LlvmVisitor visitor3 = new LlvmVisitor(Symbol_Table, buff);
                    root.accept(visitor3, Symbol_Table);
                    System.out.println("LLVM visitor finished with success!");
                    buff.close();
                }
                catch(Exception ex) {
        	        System.err.println(ex.getMessage());
        	    }
            }
            System.out.println("Finished...");
        }
        catch(ParseException ex){
            System.out.println(ex.getMessage());
        }
        catch(FileNotFoundException ex){
            System.err.println(ex.getMessage());
        }
        catch(Exception ex){
	        System.err.println(ex.getMessage());
	    }
        finally{
            try{
                if(fis != null) fis.close();
            }
            catch(IOException ex){
                System.err.println(ex.getMessage());
            }
        }
    }

    private static String Extract_Filename(String arg){
        String[] filename;
        filename = arg.split(".java");
        return filename[0] + ".ll";
    }
}
