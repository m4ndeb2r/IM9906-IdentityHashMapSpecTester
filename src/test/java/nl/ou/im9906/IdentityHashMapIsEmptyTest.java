package nl.ou.im9906;

import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#isEmpty()} method.
 */
public class IdentityHashMapIsEmptyTest {

    /**
     * Tests the normal behaviour of the method {@link IdentityHashMap#isEmpty()}.
     * The method is a pure method and has no side effects. This will also be
     * tested by checking if none of the fields will be altered.
     * <p/>
     * JML specification to test:
     * <pre>
     *   ensures
     *     \result <==> size == 0;
     * </pre>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *     assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testIsEmptyNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {

        // Create an emptry map, test pre- and postconditions
        // Precondition: class invariants hold
        // Postcondition 1: ensures \result <==> size == 0;
        // Postcondition 2: class invariants hold
        // Test if the isEmpty method is pure in these circumstances
        final IdentityHashMap<Object, Object> emptyMap = new IdentityHashMap<>();
        assertClassInvariants(emptyMap);
        assertThat((int) getValueByFieldName(emptyMap, "size"), is(0));
        assertThat(emptyMap.isEmpty(), is(true));
        assertClassInvariants(emptyMap);
        assertIsPureMethod(emptyMap, "isEmpty");

        // Create a map, and add an element to the map, and test pre- and
        // postconditions, and pureness again
        final IdentityHashMap<Object, Object> filledMap = new IdentityHashMap<>();
        filledMap.put("key1", "value1");
        assertClassInvariants(filledMap);
        assertThat((int) getValueByFieldName(filledMap, "size"), is(1));
        assertThat(filledMap.isEmpty(), is(false));
        assertClassInvariants(filledMap);
        assertIsPureMethod(filledMap, "isEmpty");
    }
}
