package nl.ou.im9906;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.TestHelper.getValueByFieldName;
import static nl.ou.im9906.TestHelper.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

public class MethodAssertions {

    /**
     * Asserts that no fields and no parameters are assigned a value during the processing of the
     * method under analysis. This conforms to the JML clause: {@code assignable \nothing}. This
     * is more or less a purity check for methods. The only difference is that pure methods also
     * conform to the JML clause: {@code \diverges false}.
     *
     * @param map        an {@link IdentityHashMap} instance, to invoke the method
     *                   under analysis on
     * @param methodName the method under analysis
     * @param params     the actual parameters that will be passed to the method
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    protected static void assertAssignableNothingClause(IdentityHashMap<Object, Object> map, String methodName, Object[] params)
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertAssignableClause(map, methodName, params, new String[0], new int[0]);
    }

    /**
     * Asserts that fields and/or parameters that are not assignable according to the JML
     * specification, do not get assigned a new value during the invocation of the method
     * under analysis.
     * </p>
     * Example: the JML specification clause {@code assignable threshold, table;} for the
     * method under test {@code init} would be testable by the following call to this method:
     * {@code assertAssignableClause(aMap, "init", new Integer[]{1024}, new String[]{"threshold", "table"}, new int[0]);}
     * </p>
     * Note 1: {@link InvocationTargetException}s are ignored. It might be the case that during invocation
     * of the method an exception is thrown. This might be expected behaviour; we might be testing
     * the assignable clause for exceptional_bevavior (in terms of JML), and we still want to check
     * the parameters and fields, regardless of any exception during invocation.
     * </p>
     * Note 2: comparison of fields and parameters is done based on the {@code toString()} of their
     * values. We do a {@code toString} of the value before invocation of the specified method, and
     * afterwards. We expect values that are not to be assigned to have the same string value before
     * and after. This is our way of "cloning" an object before and compare it with the object after
     * invocation of the method under analysis. Note this check only works for primitive fields and
     * parameters and for fields that are of a class that has a proper {@code toString} implementation.
     *
     * @param map                    an {@link IdentityHashMap} instance, to invoke the method
     *                               under analysis on
     * @param methodName             the method under analysis
     * @param params                 the actual parameters that will be passed to the method
     * @param assignableFieldNames   the names of the fields in the {@link IdentityHashMap}
     *                               that are assignable. Fields with these names will not be
     *                               checked for alteration. All other fields will be checked
     *                               for alteration.
     * @param assignableParamIndices the indices (starting at 0) of the parameters that are
     *                               assignable. Assignable parameters will not be checked
     *                               for alteration.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    protected static void assertAssignableClause(IdentityHashMap<Object, Object> map,
                                                 String methodName, Object[] params,
                                                 String[] assignableFieldNames, int[] assignableParamIndices)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {

        // Collect the fields in the IdentityHashMap: fields, their names, and their
        // values before invoking the method under test.
        final Field[] fields = map.getClass().getDeclaredFields();
        final String[] fieldNames = new String[fields.length];
        final String[] oldFieldValuesAsString = new String[fields.length];
        for (int i = 0; i < fields.length; i++) {
            fieldNames[i] = fields[i].getName();
            oldFieldValuesAsString[i] = String.valueOf(getValueByFieldName(map, fieldNames[i]));
        }

        // Collect the actual parameters passed to the method under test: their values
        // before invoking the method.
        final String[] oldParamValuesAsString = new String[params.length];
        for (int i = 0; i < params.length; i++) {
            oldParamValuesAsString[i] = String.valueOf(params[i]);
        }

        // Now, invoke the method under analysis.
        try {
            invokeMethodWithParams(map, methodName, params);
        } catch (InvocationTargetException e) {
            // This might be due to an Exception that is expected in the exceptional_behavior
            // clause of the JML. We still want to check the JML assignable clause.
            // So, let's do nothing, and resume to check the fields and parameters.
        }

        // Check if the fields have not been unexpectedly assigned a value. Compare
        // the old value with the current value.
        for (int i = 0; i < fieldNames.length; i++) {
            // Skip assignable fields for equality check
            if (!Arrays.asList(assignableFieldNames).contains(fieldNames[i])) {
                assertThat(
                        String.format("Field '%s' was unexpectedly changed.", fieldNames[i]),
                        String.valueOf(getValueByFieldName(map, fieldNames[i])),
                        is(oldFieldValuesAsString[i])
                );
            }
        }

        // Check that the parameters have not been unexpectedly assigned a value. Compare
        // the old value with the current value. Skip assignable and primitive parameters.
        for (int i = 0; i < params.length; i++) {
            // Skip assignable parameters for equality check
            if (Arrays.asList(assignableParamIndices).contains(i)) {
                continue;
            }
            // Skip primitive parameters and parameters with value null (copy-in-mechanism
            // does not require checking for assignability in these cases)
            if (params[i] == null || params[i].getClass().isPrimitive()) {
                continue;
            }
            assertThat(
                    String.format("Parameter #%d was unexpectedly changed.", i),
                    String.valueOf(params[i]),
                    is(oldParamValuesAsString[i])
            );
        }
    }

    /**
     * Asserts that a method is pure, i.e. does not have any side effect.
     *
     * @param map        the test subject
     * @param methodName the name of the method we expect to be pure
     * @param params     the actual parameters passed to the method
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     */
    protected static void assertIsPureMethod(IdentityHashMap<Object, Object> map, String methodName, Object... params)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertAssignableNothingClause(map, methodName, params);
    }

    /**
     * Asserts that a {@link IdentityHashMap} constructor is pure, i.e. does
     * not have any side effect, other than updating instance variables of
     * the class itself (this.*). Effectively it is not allowed to alter
     * any of the passed parameters.
     *
     * @param map an actual parameters passed to the constructor
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     */
    protected static void assertIsPureConstructor(Map<?, ?> map)
            throws IllegalAccessException, InvocationTargetException, NoSuchMethodException, InstantiationException {
        final String oldMapAsString = map.toString();
        final Constructor<?> constructor = IdentityHashMap.class.getDeclaredConstructor(Map.class);
        constructor.setAccessible(true);
        constructor.newInstance(map);
        assertThat(map.toString(), is(oldMapAsString));
    }

    /**
     * Determines whether a specified key-value pair is present in the
     * {@link IdentityHashMap}'s table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param key the key to search
     * @param val the value to seach
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean mappingExistsInTable(IdentityHashMap<Object, Object> map, Object key, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key && table[i + 1] == val) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified key is present in the {@link IdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param key the key to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean keyExistsInTable(IdentityHashMap<?, ?> map, Object key)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified value is present in the {@link IdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param val the value to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean valueExistsInTable(IdentityHashMap<?, ?> map, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 1; i < table.length; i += 2) {
            if (table[i] == val) {
                return true;
            }
        }
        return false;
    }


}
