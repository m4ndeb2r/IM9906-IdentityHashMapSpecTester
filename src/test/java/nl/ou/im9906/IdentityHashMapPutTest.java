package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#put(Object, Object)}
 * method.
 */
public class IdentityHashMapPutTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    private IdentityHashMap<Object, Object> map;
    private static final String KEY = "key";

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
        map.put(KEY, "aValue");
    }

    // TODO: test exceptional behaviour (IllegalStateException). Problem: memory issues...
    //  See {@link IdentityHashMapResizeTest}

    /**
     * Tests the normal bevhaviour of the {@link IdentityHashMap#put(Object, Object)}
     * method.
     * <p/>
     * Tests the followin JML specification:
     * <pre>
     *   assignable
     *     size, table, threshold, modCount;
     *   ensures
     *     // If the key already exists, size must not change, modCount must not change,
     *     // and the old value associated with the key is returned
     *     ((\exists int i;
     *         0 <= i < \old(table.length) - 1;
     *         i % 2 == 0 && \old(table[i]) == key)
     *         ==> size == \old(size) && modCount == \old(modCount) &&
     *         (\forall int j;
     *             0 <= j < \old(table.length) - 1 && j % 2 == 0;
     *             \old(table[j]) == key ==> \result == \old(table[j + 1]))) &&
     *
     *     // If the key does not exist, size must me increased by 1, modCount must change,
     *     // and null must be returned
     *     (!(\exists int i;
     *         0 <= i < \old(table.length) - 1;
     *         i % 2 == 0 && \old(table[i]) == key)
     *         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == null) &&
     *
     *     // After execution, all old keys are still present
     *     (\forall int i;
     *         0 <= i < \old(table.length) && i % 2 == 0;
     *         (\exists int j;
     *             0 <= j < table.length;
     *             j % 2 == 0 && \old(table[i]) == table[j])) &&
     *
     *     // After execution, all old values are still present, unless the old value was
     *     // associated with key
     *     (\forall int i;
     *         0 < i < \old(table.length) && i % 2 == 1;
     *         \old(table[i-1]) != key ==>
     *             (\exists int j;
     *                 0 < j < table.length;
     *                 j % 2 == 1 && \old(table[i]) == table[j])) &&
     *
     *     // After execution, the table contains the new key associated with the new value
     *     (\exists int i;
     *         0 <= i < table.length - 1 ;
     *         i % 2 == 0 && table[i] == key && table[i + 1] == value);
     * </pre>
     * Also, the class invariants are tested as a pre- and postcondition.
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testPutNormalBehaviour()
            throws IllegalAccessException, NoSuchClassException,
            NoSuchFieldException, NoSuchMethodException {
        // Test the class invariants (precondition)
        assertClassInvariants(map);

        // If the key already exists, size must not change, modCount must not change,
        // and the old value associated with the key is returned
        testPutWhenKeyAlreadyExists();

        // If the key does not exist, size must me increased by 1, modCount must change,
        // and null must be returned
        testPutWhenKeyDoesNotYetExist();

        // Test the assignability
        assertAssignableClause(map, "put", new String[]{"k", "v"}, new String[]{"size", "table", "threshold", "modCount"});

        // Test the class invariants (postcondition)
        assertClassInvariants(map);
    }

    // When key already exists ... overwrite old element
    private void testPutWhenKeyAlreadyExists() throws NoSuchFieldException, IllegalAccessException {
        final int oldSize = map.size();
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Map<Object, Object> oldEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        final Object oldValue = map.get(KEY);
        assertThat(map.put(KEY, "newValue"), is(oldValue));
        assertThat(map.size(), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        Object[] table = (Object[]) getValueByFieldName(map, "table");

        // Make sure the new element exists
        boolean found = false;
        for (int i = 0; i < table.length; i++) {
            if (KEY.equals(table[i])) {
                assertThat((String)table[i+1], is("newValue"));
                found = true;
            }
        }
        assertThat(found, is(true));

        final Map<Object, Object> newEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        // After execution, all old keys are still present
        assertThat(newEntriesAsMap.keySet().containsAll(oldEntriesAsMap.keySet()), is(true));
        // After execution, all old values, not identified by the new key, are still present
        oldEntriesAsMap.remove(KEY);
        assertThat(newEntriesAsMap.values().containsAll(oldEntriesAsMap.values()), is(true));
    }

    // When key does not yet exists ... element should be added, and null should be returned
    private void testPutWhenKeyDoesNotYetExist()
            throws NoSuchFieldException, IllegalAccessException {
        final int oldSize = map.size();
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Map<Object, Object> oldEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));

        boolean found;
        Object[] table;
        final String newKey = "newKey";
        assertThat(map.put(newKey, "otherNewValue"), nullValue());
        assertThat(map.size(), is(oldSize + 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(oldModCount));
        table = (Object[]) getValueByFieldName(map, "table");

        // Make sure the new element exists
        found = false;
        for (int i = 0; i < table.length; i++) {
            if (newKey.equals(table[i])) {
                assertThat((String)table[i+1], is("otherNewValue"));
                found = true;
            }
        }
        assertThat(found, is(true));

        final Map<Object, Object> newEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        // After execution, all old keys are still present
        assertThat(newEntriesAsMap.keySet().containsAll(oldEntriesAsMap.keySet()), is(true));
        // After execution, all old values are still present
        assertThat(newEntriesAsMap.values().containsAll(oldEntriesAsMap.values()), is(true));
    }

    private Map<Object, Object> getEntriesAsMap(Object[] table) {
        final Map<Object, Object> map = new HashMap<>();
        for (int i = 0; i < table.length; i += 2) {
            if (table[i] != null) {
                this.map.put(table[i], table[i+1]);
            }
        }
        return map;
    }

}
