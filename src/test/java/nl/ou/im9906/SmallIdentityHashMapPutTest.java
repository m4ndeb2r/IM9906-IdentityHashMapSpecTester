package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.AbstractMap;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * Because the {@link java.util.IdentityHashMap} can grow very big, some unit tests pushing the
 * class to its limits run into memory errors. Therefore we use a {@link SmallIdentityHashMap} to
 * simulate a small version of the {@link java.util.IdentityHashMap} to enable testing the limits.
 */
public class SmallIdentityHashMapPutTest {

    /**
     * Tests the exceptional_behavior case when the capacity is exhausted.
     *
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     */
    @Test
    public void testTooManyPuts()
            throws IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchFieldException,
            NoSuchClassException {

        final Object value = new Object();
        final Map<Integer, Object> smallMap = new SmallIdentityHashMap<>();
        for (int i = 0; i < 127; i++) {
            assertClassInvariants((AbstractMap<?, ?>) smallMap);
            try {
                smallMap.put(i, value);
                assertClassInvariants((AbstractMap<?, ?>) smallMap);
                if (i >= 126) {
                    fail("Expected an IllegalStateException (capacity exhausted).");
                }
            } catch (IllegalStateException e) {
                assertThat(e.getMessage(), is("Capacity exhausted."));
                assertClassInvariants((AbstractMap<?, ?>) smallMap);
            }
        }
    }

}
