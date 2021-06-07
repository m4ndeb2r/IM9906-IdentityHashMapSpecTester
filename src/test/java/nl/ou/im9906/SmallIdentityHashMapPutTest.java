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
            try {
                smallMap.put(i, value);
                if (i >= 126) {
                    fail("Expected an IllegalStatException (capacity exhausted).");
                }
            } catch (IllegalStateException e) {
                assertThat(e.getMessage(), is("Capacity exhausted."));
                assertClassInvariants((AbstractMap<?, ?>) smallMap);
            }
        }
    }

}
