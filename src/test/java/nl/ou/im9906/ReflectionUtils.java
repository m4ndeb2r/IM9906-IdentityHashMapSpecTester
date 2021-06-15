package nl.ou.im9906;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;

/**
 * Contains some generic helper methods, most of them heavily depending on
 * reflection.
 */
public class ReflectionUtils {

    /**
     * Determines whether n is a power of two.
     *
     * @param n the value to probe (>= 1)
     * @return {@code true} if n is a power of two, or {@code false} otherwise.
     * @throws IllegalArgumentException when n < 1
     */
    protected static boolean isPowerOfTwo(int n) {
        if (n < 1) {
            final String msg = String.format("Method isPowerOfTwo accepts integer values >= 1 only. Illegal value: %d.", n);
            throw new IllegalArgumentException(msg);
        }
        return (n & -n) == n;
    }

    /**
     * Returns index for Object x.
     *
     * @param x the key object for an {@link java.util.IdentityHashMap}
     * @param length the length of the internal array (table) of the {@link java.util.IdentityHashMap}
     * @return an index for the key object inside the array (table)
     */
    protected static /*@ pure @*/ int hash(Object x, int length) {
        int h =  System.identityHashCode(x);
        // Multiply by -127, and left-shift to use least bit as part of hash
        return ((h << 1) - (h << 8)) & (length - 1);
    }


    /**
     * Gets the value from a private field of an object.
     *
     * @param obj       the object containing the field
     * @param fieldName the name of the field to get the value from
     * @return the value of the specified field in the specified object
     * @throws NoSuchFieldException   if the field does not exist
     * @throws IllegalAccessException if the field cannot be accessed
     */
    protected static Object getValueByFieldName(Object obj, String fieldName)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = getFieldByNameFromClassOrParentClass(obj.getClass(), fieldName);
        return field.get(obj);
    }

    /**
     * Updates the value of a field in an object.
     *
     * @param obj       the object to contain the field that should be updated
     * @param fieldName the name of the field to update
     * @param value     the new value of the field
     * @throws NoSuchFieldException   if the field does not exist
     * @throws IllegalAccessException if the field cannot be accessed
     */
    protected static void setValueByFieldName(Object obj, String fieldName, Object value)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = getFieldByNameFromClassOrParentClass(obj.getClass(), fieldName);
        field.set(obj, value);
    }

    /**
     * Updates the value of a final field in an object.
     *
     * @param clazz     the class to contain the final static field that should be updated
     * @param fieldName the name of the final static field to update
     * @param value     the new value of the field
     * @throws NoSuchFieldException   if the field does not exist
     * @throws IllegalAccessException if the field cannot be accessed
     */
    protected static void setValueByFieldNameOfFinalStaticField(Class<?> clazz, String fieldName, Object value)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = getFieldByNameFromClassOrParentClass(clazz, fieldName);
        final Field modifiersField = Field.class.getDeclaredField("modifiers");
        modifiersField.setAccessible(true);
        modifiersField.setInt(field, field.getModifiers() & ~Modifier.FINAL);
        field.set(null, value);
        modifiersField.setInt(field, field.getModifiers() & Modifier.FINAL);
    }

    /**
     * Updates the value of a static final field of a class
     *
     * @param fieldName
     * @param value
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static void setValueOfFinalStaticFieldByName(Class<?> clazz, String fieldName, Object value)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = getFieldByNameFromClassOrParentClass(clazz, fieldName);
        Field modifiersField = Field.class.getDeclaredField("modifiers");
        modifiersField.setAccessible(true);
        modifiersField.setInt(field, field.getModifiers() & ~Modifier.FINAL);
        field.set(null, value);
    }

    /**
     * Gets the field from a class, or from the superclass. If the field is not defined
     * in the class definition of the specified class, it will recursively inspect the
     * superclass until either the field is found, or no superclass is found.
     *
     * @param clazz     the class to start searching for the specified field
     * @param fieldName the name of the required
     * @return the field, if present in the class or one of its superclasses
     * @throws NoSuchFieldException if the field could not be found
     */
    private static Field getFieldByNameFromClassOrParentClass(Class<?> clazz, String fieldName)
            throws NoSuchFieldException {
        try {
            final Field field = clazz.getDeclaredField(fieldName);
            field.setAccessible(true);
            return field;
        } catch (NoSuchFieldException e) {
            final Class<?> parent = clazz.getSuperclass();
            if (parent == null) {
                throw (e);
            }
            return getFieldByNameFromClassOrParentClass(parent, fieldName);
        }
    }

    /**
     * Invoke a method, using reflection, on the specified object, passing the specified
     * actual parameters.
     *
     * @param obj        the object to call the method on
     * @param methodName the name of the method to invoke
     * @param params     a list of actual parameters to pass to the method
     * @return the return value of the method (or Void is there is no return value)
     * @throws IllegalAccessException    if the method could not be accessed
     * @throws InvocationTargetException if the method could not be invoked
     * @throws NoSuchMethodException     if the method does not exist
     */
    protected static Object invokeMethodWithParams(Object obj, String methodName, Object... params)
            throws IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final Method[] declaredMethods = obj.getClass().getDeclaredMethods();
        for (Method method : declaredMethods) {
            if (method.getName().equals(methodName)) {
                method.setAccessible(true);
                return method.invoke(obj, params);
            }
        }
        final String msg = String.format(
                "Method '%s' not found in class '%s'.",
                methodName,
                obj.getClass().getSimpleName()
        );
        throw new NoSuchMethodException(msg);
    }

    protected static Object invokeStaticMethodWithParams(Class<?> clazz, String methodName, Object... params)
            throws IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final Method[] declaredMethods = clazz.getDeclaredMethods();
        for (Method method : declaredMethods) {
            if (method.getName().equals(methodName) && Modifier.isStatic(method.getModifiers())) {
                method.setAccessible(true);
                return method.invoke(null, params);
            }
        }
        final String msg = String.format(
                "Static method '%s' not found in class '%s'.",
                methodName,
                clazz.getSimpleName()
        );
        throw new NoSuchMethodException(msg);
    }

    protected static boolean isPrimitive(Object obj, String fieldName)
            throws NoSuchFieldException {
        return isPrimitive(obj.getClass(), fieldName);
    }

    protected static boolean isPrimitive(Class<?> clazz, String fieldName)
            throws NoSuchFieldException {
        return getFieldByNameFromClassOrParentClass(clazz, fieldName).getType().isPrimitive();
    }

    protected static boolean isFinal(Object obj, String fieldName)
            throws NoSuchFieldException {
        return isFinal(obj.getClass(), fieldName);
    }

    protected static boolean isFinal(Class<?> clazz, String fieldName)
            throws NoSuchFieldException {
        final Field field = getFieldByNameFromClassOrParentClass(clazz, fieldName);
        return Modifier.isFinal(field.getModifiers());
    }
}
