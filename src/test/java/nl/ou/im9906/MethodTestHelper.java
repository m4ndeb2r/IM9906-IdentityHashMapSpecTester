package nl.ou.im9906;

import org.hamcrest.Matcher;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPrimitive;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

public class MethodTestHelper {

    /**
     * Asserts that no fields are assigned a value during the processing of the method under
     * analysis. This conforms to the JML clause: {@code assignable \nothing}. This more or
     * less a purity check for methods. The only difference is that pure methods also
     * conform to the JML clause: {@code \diverges false}.
     * </p>
     * Example: the JML specification clause {@code assignable \nothing;} for the
     * method under test {@code someMethod}, that expects no input parameters, would be
     * testable by the following call to this method:
     * {@code assertAssignableNothingClause(anObject, "someMethod", new Object[]{});},
     * where {@code anObject} is the object to invoke the method under ananlysis on.
     *
     * @param obj        an object to invoke the method under analysis on
     * @param methodName the method under analysis
     * @param params     the actual parameters that will be passed to the method
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    protected static void assertAssignableNothingClause(Object obj, String methodName, Object[] params)
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertAssignableClause(obj, methodName, params, new String[0]);
    }

    /**
     * Asserts that fields that are not assignable according to the JML specification, do
     * not get assigned a new value during the invocation of the method under analysis.
     * </p>
     * Example: the JML specification clause {@code assignable field1, field2;} for the
     * method under test {@code someMethod}, that expects no input parameters, would be
     * testable by the following call to this method:
     * {@code assertAssignableClause(anObject, "someMethod", new Object[]{}, new String[]{"field1", "field2"});},
     * where {@code anObject} is the object to invoke the method under ananlysis on.
     * </p>
     * Note 1: {@link InvocationTargetException}s are ignored. It might be the case that during invocation
     * of the method an exception is thrown. This might be expected behaviour; we might be testing
     * the assignable clause for exceptional_bevavior (in terms of JML), and we still want to check
     * the fields, regardless of any exception during invocation.
     * </p>
     * Note 2: comparison of fields is ideally done shallow (using the '==' operator). However, the use
     * of Reflection is in our way. By retrieving the value of a private primitive field (Field.get()) we
     * always get a fresh object representation ot the primitive of the field value. With every Field.get()
     * we get a new copy (i.e. a new Integer object in case of an int, a new Long object in case of a long,
     * etc.). Therefore, in case of a pri,itive field, every comparison of the old field value and the new
     * field value using the '==' operator would return {@code false}. This is obviously not what we
     * intended. For pragmatic reasons, therefore, we will use the {@link org.hamcrest.Matchers#is(Matcher)}
     * method for primitives.
     * </p>
     * Note 3: We do not check assignability of incoming parameters. This is not necessary, because
     * Java applies the copy-in parameter mechanism. It is, therefore, impossible to assign a value
     * to the actual parameters passed to the method. Inside the method, a copy of the value is used,
     * and assigning to that copy cannot result in a side effect.
     * </p>
     * Note 4: We assume a very loose interpretation of the term 'assignable'. Any non-assignable field
     * could be assigned a value and reassigned the original value again after that, and we would not
     * notice.
     *
     * @param obj                  the object to invoke the method under analysis on
     * @param methodName           the method under analysis
     * @param params               the actual parameters that will be passed to the method
     * @param assignableFieldNames the names of the fields in the {@link IdentityHashMap}
     *                             that are assignable. Fields with these names will not be
     *                             checked for alteration. All other fields will be checked
     *                             for alteration.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    protected static void assertAssignableClause(Object obj,
                                                 String methodName, Object[] params,
                                                 String[] assignableFieldNames)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {

        // Collect the fields in the IdentityHashMap: fields, their names, and their
        // values before invoking the method under test.
        // TODO: skip final field, because they cannot be assigned anyway
        final Field[] fields = obj.getClass().getDeclaredFields();
        final String[] fieldNames = new String[fields.length];
        final Object[] oldFieldValues = new Object[fields.length];
        for (int i = 0; i < fields.length; i++) {
            fieldNames[i] = fields[i].getName();
            oldFieldValues[i] = getValueByFieldName(obj, fieldNames[i]);
        }

        // Now, invoke the method under analysis.
        try {
            invokeMethodWithParams(obj, methodName, params);
        } catch (InvocationTargetException e) {
            // This might be due to an Exception that is expected in the
            // exceptional_behavior heavy weight specification case of the JML.
            // We still want to check the JML assignable clause. So, let's do
            // nothing, and resume to check the fields and parameters.
        }

        // Check if the fields have not been unexpectedly assigned a value.
        // I.e. (according to our 'loose' interpretation of the term 'assignable')
        // compare the old value with the current value.
        for (int i = 0; i < fieldNames.length; i++) {
            // Skip assignable fields for assignability check
            if (!Arrays.asList(assignableFieldNames).contains(fieldNames[i])) {
                final Object newFieldValue = getValueByFieldName(obj, fieldNames[i]);
                if (isPrimitive(obj, fieldNames[i])) {
                    // In case of a primitive field, we cannot use the '==' operator,
                    // because getValuesByFieldName returns an object representation of the
                    // actual reference to the respective field. We, therefore, use Matchers.is()
                    assertOldEqualsNewPrimitive(fieldNames[i], newFieldValue, oldFieldValues[i]);
                } else {
                    // In case of a non-primitive field, we can use the '==' operator,
                    // because getValuesByFieldName returns the actual reference to the
                    // respective object.
                    assertOldSameAsNewNonPrimitive(fieldNames[i], newFieldValue, oldFieldValues[i]);
                }
            }
        }
    }

    private static void assertOldSameAsNewNonPrimitive(String fieldName, Object newFieldValue, Object oldFieldValue) {
        final String msg = String.format(
                "Non-primitive, non-assignable field '%s' unexpectedly assigned.",
                fieldName
        );
        assertThat(msg, newFieldValue == oldFieldValue, is(true));
    }

    private static void assertOldEqualsNewPrimitive(String fieldName, Object newFieldValue, Object oldFieldValue) {
        final String msg = String.format(
                "Primitive, non-assignable field '%s' unexpectedly changed.",
                fieldName
        );
        assertThat(msg, newFieldValue, is(oldFieldValue));
    }

    /**
     * Asserts that a method is pure, i.e. does not have any side effect.
     *
     * @param obj        the object to call the method on
     * @param methodName the name of the method we expect to be pure
     * @param params     the actual parameters passed to the method
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     */
    protected static void assertIsPureMethod(Object obj, String methodName, Object... params)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertAssignableNothingClause(obj, methodName, params);
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
    @Deprecated
    // TODO: during our meetin on July 24th, we discussed the assignable clause with regard to parameters.
    //   We concluded that, since Java only supports the copy-in parameter mechanism, it is unnecessary to
    //   check if parameters are being assigned. This method, therefore, has become superfluous.
    //   The question arises, however, what Leavens et al. might have meant when they describe pure constructors
    //   in section 7.1.1.3 of their JML Reference. Pure constructors, according to the JML reference have the
    //   clauses: diverges false; assignable this.*;. Wouldn't this assignable clause be superfluous when
    //   assignable clauses never have ant effect on (copied-in) parameters?
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
     * @param val the value to search
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
