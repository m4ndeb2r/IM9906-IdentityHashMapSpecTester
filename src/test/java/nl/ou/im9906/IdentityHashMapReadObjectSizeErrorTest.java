package nl.ou.im9906;

import org.junit.Test;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the {@link IdentityHashMap#readObject(ObjectInputStream)} method, and shows that,
 * due to a bug, the {@link IdentityHashMap#size} value is never set (stays 0).
 * </p>
 * Note: the {@link IdentityHashMap#readObject(ObjectInputStream)} method is a private method
 * that is used by Java's Serialization Framework.
 */
public class IdentityHashMapReadObjectSizeErrorTest {

    // The number of mappings in the input stream
    private static final int NUMBER_OF_MAPPINGS_IN_INPUTSTREAM = 3;

    // Boolean flag to indicate if errors are expected, or correct behaviour is expected
    // Flip this value to false if the readObject method is expected to work correctly, or to
    // false if the readObject method is expected to contain the size bug.
    private static final boolean EXPECT_ERROR = true;

    /**
     * Shows that the readObject method (in certain situations) does not update the field
     * {@link IdentityHashMap#size}
     */
    @Test
    public void testSizeError()
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

        // This will result in a map containing 10 entries, but has size == 0.
        invokeMethodWithParams(map, "readObject", inputStream);

        // Test the size of the array table
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        final int len = table.length;
        assertThat(len, is(16));

        // Test the number or entries added to the array table
        List<Object> keys = new ArrayList<>();
        for (int i = 0; i < len; i += 2) {
            if (table[i] != null)
                keys.add(table[i]);
        }
        assertThat(keys.size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));

        if (EXPECT_ERROR) {
            // The following tests SUCCEED because we anticipate a bug in readObject (size is not correctly set)
            assertThat(map.size(), is(0));
            assertThat(map.isEmpty(), is(true));
            assertThat(map.keySet().size(), is(0));
            assertThat(map.keySet().isEmpty(), is(true));
            assertThat(map.keySet().toArray().length, is(0));
            assertThat(map.values().size(), is(0));
            assertThat(map.values().isEmpty(), is(true));
            assertThat(map.values().toArray().length, is(0));
            map.remove(keys.get(0));
            assertThat(map.size(), is(-1));
            map.remove(keys.get(1));
            assertThat(map.size(), is(-2));
        } else {
            // The following tests FAIL because we expect readObject to correctly set the size field
            assertThat(map.size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));
            assertThat(map.isEmpty(), is(false));
            assertThat(map.keySet().size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));
            assertThat(map.keySet().isEmpty(), is(false));
            assertThat(map.keySet().toArray().length, is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));
            assertThat(map.values().size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));
            assertThat(map.values().isEmpty(), is(false));
            assertThat(map.values().toArray().length, is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM));
            map.remove(keys.get(0));
            assertThat(map.size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM - 1));
            map.remove(keys.get(1));
            assertThat(map.size(), is(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM - 2));
        }
    }

}
