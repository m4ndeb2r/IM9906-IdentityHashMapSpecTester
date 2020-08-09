package nl.ou.im9906;

import org.junit.Test;

import java.util.Collection;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap.Values#size()} method.
 */
public class IdentityHashMapValuesSizeTest {

    /**
     * Tests the normal behaviour of the method {@link IdentityHashMap.Values#size()}.
     * The size method is a pure method and has no side effects. This will be
     * tested by checking if none of the fields will be altered. There is no
     * precondition specified for the method, so only the class invariant should
     * hold as a precondition (and as a postcondition as well, obviously).
     * <p/>
     * JML specification to check:
     * <pre>
     *   ensures
     *     \result == size;
     * </pre>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *   assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testValuesSizeNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        map.put("key1", "value1");
        map.put("key2", "value2");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Postcondition: result == size
        assertThat(map.values().size(), is((int) getValueByFieldName(map, "size")));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the size method is pure
        // TODO: this only tests the fields of the IdentityHashMap.Values class, not the
        //  fields of the IdentityHashMap class.
        assertIsPureMethod(map.values(), "size");
    }

}
