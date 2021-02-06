package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

public class SmallIdentityHashMapConstructorTest {

    @Test
    public void testConstructorWithTooBigMapAsArgument()
            throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {

        final Object value = new Object();
        final Map<Integer, Object> paramMap = new HashMap<>();
        for (int i = 0; i < 127; i++) {
            paramMap.put(i, value);
        }
        try {
            new SmallIdentityHashMap<>(paramMap);
            fail("Expected an IllegalStatException (capacity exhausted).");
        } catch (IllegalStateException e) {
            assertThat(e.getMessage(), is("Capacity exhausted."));
        }
    }

    @Test
    public void testConstructorWithMapThatAlmostFillsTheTableAsArgument()
            throws
            IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchFieldException,
            NoSuchClassException {

        final Object value = new Object();
        final Map<Integer, Object> paramMap = new HashMap<>();
        for (int i = 0; i < 126; i++) {
            paramMap.put(i, value);
        }
        final SmallIdentityHashMap<Integer, Object> smallMap = new SmallIdentityHashMap<>(paramMap);
        assertClassInvariants(smallMap);
    }

}
