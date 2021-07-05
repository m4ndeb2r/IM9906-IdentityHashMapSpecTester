package nl.ou.im9906;

import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#size()} method.
 */
public class IdentityHashMapSizeTest {

    /**
     * Tests the normal behaviour of the method {@link IdentityHashMap#size()}.
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
     * Also tests the purity of the constructor, meaning (in terms of JML):
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
    public void testSizeNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();

        for(int i = 0; i < 666; i++) {
            map.put(new String("key"), new String("value"));
            // Test if the class invariants hold (precondition)
            assertClassInvariants(map);
            // Postcondition: result == size
            assertThat(map.size(), is(i+1));
            assertThat((int) getValueByFieldName(map, "size"), is(i+1));
            // Test if the class invariants hold (postcondition)
            assertClassInvariants(map);
        }

        // Test if the size method is really pure
        assertIsPureMethod(map, "size");
    }

}
