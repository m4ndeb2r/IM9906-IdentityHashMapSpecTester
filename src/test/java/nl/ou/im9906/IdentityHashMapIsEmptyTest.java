package nl.ou.im9906;

import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantsAssertions.assertClassInvariants;
import static nl.ou.im9906.MethodAssertions.assertIsPureMethod;
import static nl.ou.im9906.TestHelper.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#isEmpty()} method.
 */
public class IdentityHashMapIsEmptyTest {

    /**
     * Tests the postconditions of the isEmpty method of the {@link IdentityHashMap}.
     * The isEmpty method is a pure method and has no side effects. This will also be
     * tested by checking if none of the fields will be altered.
     * </p>
     * JML specification to test:
     * <pre>
     *     also
     *       public normal_behavior
     *         ensures
     *           \result <==> size == 0;
     * </pre>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *     assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testIsEmptyNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {

        // Create an emptry map, test pre- and postconditions
        // Precondition: class invariants hold
        // Postcondition 1: ensures \result <==> size == 0;
        // Postcondition 2: class invariants hold
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        assertClassInvariants(map);
        assertThat((int) getValueByFieldName(map, "size"), is(0));
        assertThat(map.isEmpty(), is(true));
        assertClassInvariants(map);

        // Add an element to the map, and test pre- and
        // postconditions agian
        map.put("key1", "value1");
        assertClassInvariants(map);
        assertThat((int) getValueByFieldName(map, "size"), is(1));
        assertThat(map.isEmpty(), is(false));
        assertClassInvariants(map);

        // Test if the isEmpty method is pure
        assertIsPureMethod(map, "isEmpty");
    }
}
