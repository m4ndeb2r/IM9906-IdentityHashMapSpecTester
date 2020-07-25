package nl.ou.im9906;

import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#capacity(int)} method.
 * TODO: after JML spec is complete, extend this test class
 */
public class IdentityHashMapCapacityTest {

    /**
     * Tests if the private method {@link IdentityHashMap#capacity(int)} is pure.
     * Furthermore, tests if the class invariant holds as a precondition and as a
     * postcondition.
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testCapacityIsPure()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {
        // Create an instance of the IdentityHashMap
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Test if the method is pure
        assertIsPureMethod(map, "capacity", 32);

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }
}
