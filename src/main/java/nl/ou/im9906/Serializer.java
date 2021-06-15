package nl.ou.im9906;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.IdentityHashMap;

/**
 * Serializes and deserializes an {@link IdentityHashMap}.
 */
public class Serializer {

    public static void main(String[] args) throws IOException {
        // Create an object containing an IdentityHashMap
        final SerializableObject serializableObject = new SerializableObject();

        // Add two elements to the IdentityHashMap
        serializableObject.getIdentityHashMap().put("key1", "value1");
        serializableObject.getIdentityHashMap().put("key2", "value2");
        System.out.println("size = " + serializableObject.getIdentityHashMap().size());

        // Serialize the object
        final String filename = "file.ser";
        serialize(serializableObject, filename);

        // Deserialize the object
        final SerializableObject deserializedObject = deserialize(filename);

        // Check the size() method
        System.out.println("size = " + deserializedObject.getIdentityHashMap().size());

        // Compares with the original
        if (serializableObject.getIdentityHashMap().equals(deserializedObject.getIdentityHashMap())) {
            System.out.println("Deserialized object is equal to the original");
        } else {
            System.out.println("Deserialized object is NOT equal to the original");
        }
    }

    private static SerializableObject deserialize(String filename) throws IOException {
        SerializableObject object = null;
        FileInputStream file = null;
        ObjectInputStream in = null;

        try {
            // Reading the object from a file
            file = new FileInputStream(filename);
            in = new ObjectInputStream(file);

            // Method for deserialization of object
            object = (SerializableObject) in.readObject();
            System.out.println("Object has been deserialized");

        } catch (IOException ex) {
            System.out.println("IOException is caught; object not deserialized");
        } catch (ClassNotFoundException ex) {
            System.out.println("ClassNotFoundException is caught; object not deserialized");
        } finally {
            if (in != null) in.close();
            if (file != null) file.close();
        }
        return object;
    }

    private static void serialize(SerializableObject object, String filename) throws IOException {
        // Serialization
        FileOutputStream file = null;
        ObjectOutputStream out = null;
        try {
            //Saving of object in a file
            file = new FileOutputStream(filename);
            out = new ObjectOutputStream(file);

            // Method for serialization of object
            out.writeObject(object);
            System.out.println("Object has been serialized");

        } catch (IOException ex) {
            System.out.println("IOException is caught; object not serialized");
        } finally {
            if (out != null) out.close();
            if (file != null) file.close();
        }
    }

    static class SerializableObject implements java.io.Serializable {
        private IdentityHashMap<String, String> map = new IdentityHashMap<>();

        public IdentityHashMap<String, String> getIdentityHashMap() {
            return map;
        }
    }
}
