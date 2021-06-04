package nl.ou.im9906;

import org.junit.Test;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static junit.framework.TestCase.fail;
import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;

/**
 * Tests the {@link IdentityHashMap#readObject(ObjectInputStream)} method, and shows that,
 * due to an overflow error in the {@link IdentityHashMap#capacity(int)} method will result
 * in the {@link IdentityHashMap#nextKeyIndex(int, int)} method to go into an infinite loop.
 * The method {@link IdentityHashMap#readObject(ObjectInputStream)} violates the class invariant
 * by filling up the {@link IdentityHashMap#table} completely.
 * </p>
 * Note: the {@link IdentityHashMap#readObject(ObjectInputStream)} method is a private method
 * that is used by Java's Serialization Framework. When an attacker modifies serialized
 * {@link IdentityHashMap} instance in a way that the number of mappings triggers the overflow
 * error, this problem can actually occur in practice.
 */
public class IdentityHashMapReadObjectOverflowTest {

    // The number of mappings in the input stream (1073741826 mappings (3/4 * 1431655768))
    private static final int NUMBER_OF_MAPPINGS_IN_INPUTSTREAM = 1073741826;

    /**
     * Shows that the readObject method (in certain situations) never terminates. Due
     * to an overflow error in the method {@link IdentityHashMap#capacity(int)}, the
     * {@link IdentityHashMap#table} will be completely filled up, violating the following
     * class invariant:
     * <pre>
     *   // Table must have at least one empty key-element to prevent
     *   // infinite loops when a key is not present.
     *   public invariant
     *     (\exists \bigint i;
     *         0 <= i < table.length / (\bigint)2;
     *         table[2 * i] == null);
     *   </pre>
     */
    @Test
    public void testOverflowError()
            throws IllegalAccessException, NoSuchClassException,
            NoSuchFieldException, IOException,
            InvocationTargetException, NoSuchMethodException,
            ClassNotFoundException {

        // Create an IdentityHashMap and test if the class invariant holds initially
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        assertClassInvariants(map);

        // We need a mock inputstream to simulate the context in which the overflow error
        // to emerge without having to deal with memory issues and large input files.
        final ObjectInputStream inputStream = new MockObjectInputStream(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM);

        // This will result in an infinite loop in the {@link SmallIdentityHashMap#putForCreate} method.
        invokeMethodWithParams(map, "readObject", inputStream);

        // We will never get to this point; if we do, however, our hypothesis failed
        fail("Unexpected state. Due to a know overflow error, readObject() was not expected to finish.");
    }

}
