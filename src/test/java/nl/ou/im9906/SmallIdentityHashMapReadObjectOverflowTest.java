package nl.ou.im9906;

import junit.framework.TestCase;
import org.junit.Test;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * A test attempting to add 129 entries to a {@link SmallIdentityHashMap}, with a MAXIMUM_CAPACITY of
 * 128. This will result in an infinite loop in {@link SmallIdentityHashMap#putForCreate(Object, Object)}.
 * All elements in the array {@link SmallIdentityHashMap#table} will be filled up, violating the requirement
 * of at least one key-element to stay empty.
 */
public class SmallIdentityHashMapReadObjectOverflowTest {

    // The number of mappings in the input stream (129 mappings)
    private static final int NUMBER_OF_MAPPINGS_IN_INPUTSTREAM = 129;

    @Test
    public void testOverflowError()
            throws IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchFieldException,
            NoSuchClassException, IOException {

        final SmallIdentityHashMap<Integer, Object> smallMap = new SmallIdentityHashMap<>();
        assertClassInvariants(smallMap);

        // We need a mock inputstream to simulate the context in which the overflow error
        // to emerge without having to deal with memory issues and large input files.
        final ObjectInputStream inputStream = new nl.ou.im9906.MockObjectInputStream(NUMBER_OF_MAPPINGS_IN_INPUTSTREAM);

        // This will result in an infinite loop in the {@link SmallIdentityHashMap#putForCreate} method.
        invokeMethodWithParams(smallMap, "readObject", inputStream);

        // We will never get to this point; if we do, however, our hypothesis failed
        TestCase.fail("Unexpected state. Due to a know overflow error, readObject() was not expected to finish.");
    }

}
