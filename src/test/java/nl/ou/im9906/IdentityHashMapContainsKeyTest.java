package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.MethodTestHelper.keyExistsInTable;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#containsKey(Object)}
 * method.
 */
public class IdentityHashMapContainsKeyTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsKey(Object)} method,
     * whether or not a key is present in the table.
     * <p/>
     * Tests the following JML postcondition:
     * <pre>
     *   \result <==> (\exists int i;
     *      0 <= i < table.length - 1;
     *      i % 2 == 0 && table[i] == maskNull(key));
     * </pre>
     * Also tests if the method is pure, and checks if the class invariants hold
     * before and after invocation of the method.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testContainsKeyNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {
        assertContainsKeyBehaviourFound(map);
        assertContainsNullKeyBehaviourFound(map);
        assertContainsKeyBehaviourNotFound(map);
    }


    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsKey(Object)} method,
     * when a key is present in the table. Also, the pureness of the method is tested.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    private void assertContainsKeyBehaviourFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        assertThat(map.containsKey(key), is(false));

        map.put(key, "aValue");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method
        final boolean found = keyExistsInTable(map, key);

        // Check the method's postcondition
        assertThat(map.containsKey(key), is(found));
        assertThat(found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsKey method is pure
        assertIsPureMethod(map, "containsKey", key);
    }

    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsKey(Object)} method,
     * when a key is present in the table. Also, the pureness of the method is tested.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    private void assertContainsNullKeyBehaviourFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = null;
        assertThat(map.containsKey(key), is(false));

        map.put(key, "aValue");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method
        final Object maskedNullKey = ReflectionUtils.getValueByFieldName(map, "NULL_KEY");
        final boolean found = keyExistsInTable(map, maskedNullKey);

        // Check the method's postcondition
        assertThat(map.containsKey(key), is(found));
        assertThat(found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsKey method is pure
        assertIsPureMethod(map, "containsKey", key);
    }

    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsKey(Object)} method,
     * when a key is NOT present in the table. Also, the pureness of the method is tested.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    private void assertContainsKeyBehaviourNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        map.put(key, "aValue");
        final String anotherKey = "anotherKey";

        // Precondition: the class invariant should hold
        assertClassInvariants(map);

        // Call the method
        final boolean found = keyExistsInTable(map, anotherKey);

        // Check the method's postcondition
        assertThat(map.containsKey(anotherKey), is(found));
        assertThat(found, is(false));

        // Postcondition: the class invariant should hold
        assertClassInvariants(map);

        // Test if the containsKey method is pure
        assertIsPureMethod(map, "containsKey", anotherKey);
    }
}
