package nl.ou.im9906;

import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#clone()}
 * method.
 * TODO: after JML spec is complete, extend this test class
 */
public class IdentityHashMapCloneTest {

    /**
     * Tests if the method {@link IdentityHashMap#clone()} is a pure method,
     * as specified in the JML. Furthermore, as a precondition as well a postcondition,
     * the class invariants should hold, obviously.
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testCloneNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {
        // Create a new IdentityHashMap
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        map.put("aKey", "aValue");
        map.put("anotherKey", "anotherValue");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the clone method, and check if it is pure
        assertIsPureMethod(map, "clone");

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }

}
