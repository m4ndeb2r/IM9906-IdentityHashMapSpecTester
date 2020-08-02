package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.MethodTestHelper.mappingExistsInTable;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#get(Object)}
 * method.
 */
public class IdentityHashMapGetTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Test if the normal behaviour of the {@link IdentityHashMap#get(Object)} method
     * for several cases. Also, the pureness of the method is tested.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testGetPostcondition()
            throws InvocationTargetException, NoSuchMethodException,
            IllegalAccessException, NoSuchFieldException,
            NoSuchClassException {
        assertGetPostConditionForNonNullResult(map);
        assertGetPostConditionForNullResult(map);
    }

    /**
     * Tests the normal behaviour of the {@link IdentityHashMap#get(Object)}
     * method when a non-{@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertGetPostConditionForNonNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "key";
        final String val = "val";
        map.put(key, val);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Assert that the following postcondition holds:
        //   \result != null <==>
        //       (\exists \bigint i;
        //           0 <= i < table.length - 1 && i % 2 == 0;
        //           table[i] == key && \result == table[i + 1])
        final boolean found = mappingExistsInTable(map, key, val);
        assertThat(map.get(key) != null && found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionForNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        // Assert that the following postcondition holds:
        //     \result == null <==>
        //         (!(\exists \bigint i;
        //             0 <= i < table.length - 1 && i % 2 == 0;
        //             table[i] == key) ||
        //        (\exists \bigint i;
        //             0 <= i < table.length - 1 && i % 2 == 0;
        //             table[i] == key && table[i + 1] == null)
        //         );
        assertGetPostConditionKeyNotFound(map);
        assertGetPostConditionValueNull(map);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because the key is not
     * found.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     * @throws NoSuchClassException
     */
    private void assertGetPostConditionKeyNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        final String anotherKey = new String("aKey");
        final String val = "aValue";
        map.put(key, val);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final boolean valueFound = mappingExistsInTable(map, anotherKey, val);
        assertThat(map.get(anotherKey) == null, is(true));
        assertThat(valueFound, is(false));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because however the key
     * is found, the value is actually {@code null}.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionValueNull(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "KEY";
        final String val = null;
        map.put(key, val);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final boolean valueFound = mappingExistsInTable(map, key, val);
        assertThat(map.get(key) == null, is(true));
        assertThat(valueFound, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

}
