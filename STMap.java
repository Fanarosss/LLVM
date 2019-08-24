import java.util.*;

public class STMap {

    public static abstract class Level {
        public String name;
        public String type;
        public int offset;
        public String get_name(){return null;}
        public String get_superclass(){return null;}
        public String get_parentclass(){return null;}
        public int get_offset(){return 0;}
        public int get_mthd_offset(){return 0;}
        public void add_class(ClassST cl){}
        public ClassST get_class(String cl_name){return null;}
        public boolean exists_class(String cl_name){return false;}
        public boolean exists_method(String mthd_name){return false;}
        public boolean exists_var(String var_name){return false;}
        public void add_method(MethodST mthd){}
        public MethodST get_method(String mthd_name){return null;}
        public void add_variable(VariableDL var){}
        public VariableDL get_variable(String var_name){return null;}
        public void increment_offset(String type){}
        public void increment_mthd_offset() {}
        public String get_arg_type(int index){return null;}
        public String get_arg_name(int index){return null;}
        public void add_arg_type(String a){}
        public void add_arg_name(String a){}
        public int num_args(){return 0;}
        public int get_method_number(){return 0;}
        public String get_type(){return null;}
        public void merge_scopes(ClassST pcl){}
        public List<String> get_all_classes(){return null;}
        public HashMap<Integer,MethodST> get_all_methods(){return null;}
        public void new_vtable(List<String> vt){}
        public List<String> get_vtable(){return null;}
        public int find_pos_in_vtable(String mthd_name){return 0;}
    }

    public static class SymTable extends Level {

        LinkedHashMap<String, ClassST> Classes = new LinkedHashMap<String, ClassST>();

        public void add_class(ClassST cl) {
    		Classes.put(cl.name, cl);
    	}

        public ClassST get_class(String cl_name) {
    		if(Classes.isEmpty()) return null;
    		return Classes.get(cl_name);
    	}

    	public boolean exists_class(String cl_name) {
    		return Classes.containsKey(cl_name);
    	}

        public String get_type(){
            return "stable";
        }

        public List<String> get_all_classes() {
            List<String> cls = new ArrayList<String>();
            for (Map.Entry<String, ClassST> entry : Classes.entrySet()){
                cls.add(entry.getValue().name);
            }
            return cls;
        }
    }

    public static class ClassST extends Level {
        public String name;
        public String parentclass = null;
        public String superclass = null;
        public int offset = 0;
        public boolean is_mainclass = false;
        public int mthd_offset = 0;
        HashMap<String, VariableDL> Variables = new HashMap<String, VariableDL>();
        HashMap<String, MethodST> Methods = new HashMap<String, MethodST>();
        List<String> vtable;

        public String get_name(){
            return name;
        }

        public String get_superclass(){
            return superclass;
        }

        public int get_offset(){
            return offset;
        }

        public int get_mthd_offset(){
            return mthd_offset;
        }

        public void add_method(MethodST mthd) {
            Methods.put(mthd.name, mthd);
        }

        public MethodST get_method(String mthd_name) {
            if(Methods.isEmpty()) return null;
    		return Methods.get(mthd_name);
        }

        public boolean exists_method(String mthd_name){
            return Methods.containsKey(mthd_name);
        }

        public void add_variable(VariableDL var) {
            Variables.put(var.name, var);
        }

        public VariableDL get_variable(String var_name) {
            if(Variables.isEmpty()) return null;
            return Variables.get(var_name);
        }

        public boolean exists_var(String var_name) {
            return Variables.containsKey(var_name);
        }

        public void increment_offset(String type) {
            if (type.equals("int")) {
                offset += 4;
            } else if (type.equals("boolean")) {
                offset += 1;
            } else if (type.equals("pointer")) {
                offset += 8;
            }
        }

        public void increment_mthd_offset() {
            mthd_offset += 8;
        }

        public String get_type(){
            return "class";
        }

        public void merge_scopes(ClassST cl){
            for (Map.Entry<String, VariableDL> entry : Variables.entrySet()) {
                String name = entry.getKey();
                VariableDL var = entry.getValue();
                if (!cl.exists_var(name)) cl.add_variable(var);
            }

            for (Map.Entry<String, MethodST> entry : Methods.entrySet()) {
                String name = entry.getKey();
                MethodST mthd = entry.getValue();
                if (!cl.exists_method(name)) {
                    cl.add_method(mthd);
                } else {
                    /* when there is overriding */
                    cl.get_method(name).offset = mthd.offset;
                }
            }
        }

        public int get_method_number(){
            return Methods.size();
        }

        public HashMap<Integer,MethodST> get_all_methods() {
            HashMap<Integer,MethodST> mthds = new HashMap<Integer,MethodST>();
            for (Map.Entry<String, MethodST> entry : Methods.entrySet()){
                mthds.put(entry.getValue().get_offset(),entry.getValue());
            }
            return mthds;
        }

        public void new_vtable(List<String> vt) {
            vtable = vt;
        }

        public List<String> get_vtable() {
            return vtable;
        }

        public int find_pos_in_vtable(String mthd_name){
            int pos = 0;
            for (String name : vtable){
                if (mthd_name.equals(name)){
                    break;
                }
                pos++;
            }
            return pos;
        }
    }

    public static class MethodST extends Level {
        public String name;
        public String parentclass = null;
        public String type;
        public boolean overiding = false;
        public int offset = 0;
        public List<String> args_type = new ArrayList<String>();
        public List<String> args_name = new ArrayList<String>();
        HashMap<String, VariableDL> Variables = new HashMap<String, VariableDL>();

        public String get_name(){
            return name;
        }

        public int get_offset(){
            return offset;
        }

        public String get_arg_type(int index){
            return args_type.get(index);
        }

        public void add_arg_type(String a){
            args_type.add(a);
        }

        public String get_arg_name(int index){
            return args_name.get(index);
        }

        public void add_arg_name(String a){
            args_name.add(a);
        }

        public int num_args(){
            return args_type.size();
        }

        public String get_parentclass(){
            return parentclass;
        }

        public void add_variable(VariableDL var) {
            Variables.put(var.name, var);
        }

        public VariableDL get_variable(String var_name) {
            if(Variables.isEmpty()) return null;
            return Variables.get(var_name);
        }

        public boolean exists_var(String var_name){
            return Variables.containsKey(var_name);
        }

        public void increment_offset(String type) {
            if (type.equals("int")) {
                offset += 4;
            } else if (type.equals("boolean")) {
                offset += 1;
            } else if (type.equals("pointer")) {
                offset += 8;
            }
        }

        public String get_type(){
            return "method";
        }
    }

    public static class VariableDL extends Level {
        public String name;
        public String parentname;
        public String type;
        public int offset = 0;

        public String get_name(){
            return name;
        }

        public int get_offset(){
            return offset;
        }

        public String get_parentclass(){
            return parentname;
        }

    }
}
