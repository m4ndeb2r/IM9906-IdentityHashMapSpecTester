package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.invokeStaticMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#hash(Object, int)}
 * method.
 * TODO: after JML spec is complete, extend this test class
 */
public class IdentityHashMapHashTest {

    /**
     * Tests if the method {@link IdentityHashMap#hash(Object, int)} is a pure method,
     * as specified in the JML. Furthermore, as a precondition as well a postcondition,
     * the class invariants should hold, obviously.
     * <p>
     * The JML being tested:
     * <pre>
     *   private normal_behavior
     *     requires
     *       x != null;
     *     ensures
     *       \result == \dl_genHash(x, length) &&
     *       \result < length &&
     *       \result >=0;
     *   also
     *     private normal_behavior
     *       requires
     *         x == null;
     *       ensures
     *         \result == 0;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if one of the methods could not be invoked
     */
    @Test
    public void testHashNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Create a new IdentityHashMap
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Test the return value of the hash method when first param == null
        final Integer zeroHash = (Integer) invokeStaticMethodWithParams(IdentityHashMap.class, "hash", null, 256);
        assertThat(zeroHash, is(0));

        // Test the return value of the hash method when first param != null
        final Integer hash = (Integer) invokeStaticMethodWithParams(IdentityHashMap.class, "hash", new Object(), 2);
        assertThat(hash, lessThan(2));
        assertThat(hash, greaterThanOrEqualTo(0));

        // Call the hash method, and check if it is pure
        assertIsPureMethod(map, "hash", new Object(), 32);

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }

}
