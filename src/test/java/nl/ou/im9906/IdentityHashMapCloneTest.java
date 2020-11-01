package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#clone()}
 * method.
 */
public class IdentityHashMapCloneTest {

    /**
     * Tests if the method {@link IdentityHashMap#clone()} is a pure method,
     * as specified in the JML. Furthermore, as a precondition as well a postcondition,
     * the class invariants should hold, for normal behaviour.
     * <p/>
     * JML specification tested:
     * <pre>
     *   public normal_behavior
     *     ensures
     *       ((VerifiedIdentityHashMap)\result).size == size &&
     *       ((VerifiedIdentityHashMap)\result).threshold == threshold &&
     *       ((VerifiedIdentityHashMap)\result).entrySet == null &&
     *       ((VerifiedIdentityHashMap)\result).values == null &&
     *       ((VerifiedIdentityHashMap)\result).keySet == null &&
     *       (\forall i;
     *         0 <= i && i < table.length;
     *         table[i] == ((VerifiedIdentityHashMap)\result).table[i]) &&
     *       \invariant_for((VerifiedIdentityHashMap)\result);
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testCloneNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {
        // Create a new IdentityHashMap
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        map.put("aKey", "aValue");
        map.put("anotherKey", "anotherValue");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method under test
        final IdentityHashMap<Object, Object> clone = (IdentityHashMap<Object, Object>) map.clone();

        // Test poscondition
        final int mapSize = (int) getValueByFieldName(map, "size");
        final int cloneSize = (int) getValueByFieldName(clone, "size");
        assertThat(cloneSize, is(mapSize));

        final int mapThreshold = (int) getValueByFieldName(map, "threshold");
        final int cloneThreshold = (int) getValueByFieldName(clone, "threshold");
        assertThat(cloneThreshold, is(mapThreshold));

        assertThat(getValueByFieldName(clone, "entrySet"), nullValue());
        assertThat(getValueByFieldName(clone, "values"), nullValue());
        assertThat(getValueByFieldName(clone, "keySet"), nullValue());

        final Object[] mapTable = (Object[]) getValueByFieldName(map, "table");
        final Object[] cloneTable = (Object[]) getValueByFieldName(clone, "table");
        assertThat(mapTable.length, is(cloneTable.length));
        for (int i = 0; i < mapTable.length; i++) {
            assertThat(mapTable[i] == cloneTable[i], is(true));
        }

        // Test if the class invariants hold
        assertClassInvariants(map);
        assertClassInvariants(clone);

        // Call the clone method to check if it is pure
        assertIsPureMethod(map, "clone");
    }
}
