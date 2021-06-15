package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.MethodTestHelper.valueExistsInTable;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#containsValue(Object)}
 * method.
 */
public class IdentityHashMapContainsValueTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the normal behavhiour of the {@link IdentityHashMap#containsValue(Object)}
     * whether or not a value is present in the table.
     * <p/>
     * Tests the following JML postcondition:
     * <pre>
     *     \result <==> (\exists int i;
     *         1 <= i < table.length;
     *         i % 2 == 0 && table[i] == value);
     * </pre>
     * Also tests if the method is pure, and checks if the class invariants hold
     * before and after invocation of the method.
     *
     * @param map the map to call the containsValue method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testContainsValuePostcondition()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {
        assertContainsValuePostConditionFound(map);
        assertContainsValuePostConditionNotFound(map);
    }

    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsValue(Object)} method,
     * when a value is present in the table. Also, the pureness of the method is tested.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    private void assertContainsValuePostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method
        final boolean found = valueExistsInTable(map, value);

        // Check the method's postcondition
        assertThat(map.containsValue(value), is(found));
        assertThat(found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsValue", value);
    }

    /**
     * Checks the normal behaviour the {@link IdentityHashMap#containsValue(Object)} method,
     * when a value is NOT present in the table. Also, the pureness of the method is tested.
     *
     * @param map the map to call the containsValue method on
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    private void assertContainsValuePostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);
        final String anotherValue = "anotherValue";

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method
        final boolean found = valueExistsInTable(map, anotherValue);

        // Check the method's postcondition
        assertThat(map.containsValue(anotherValue), is(found));
        assertThat(found, is(false));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsValue", anotherValue);
    }
}
