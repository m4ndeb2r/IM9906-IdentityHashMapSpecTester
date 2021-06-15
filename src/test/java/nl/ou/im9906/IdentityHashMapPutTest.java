package nl.ou.im9906;

import junit.framework.AssertionFailedError;
import org.junit.Before;
import org.junit.Test;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.setValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#put(Object, Object)}
 * method.
 *
 * Note: this test does not test loop invariants and block contracts that were used to
 * specify the put method. Therefore, this test is by far not a complete test for the
 * JML specification.
 */
public class IdentityHashMapPutTest {

    private IdentityHashMap<Object, Object> map;
    private static final String KEY = "key";
    private Object maskedNullKey;

    @Before
    public void setUp()
            throws NoSuchFieldException, IllegalAccessException {
        map = new IdentityHashMap<>();
        maskedNullKey = getValueByFieldName(map, "NULL_KEY");
        map.put(KEY, "aValue");
        map.put(null, "anotherValue");
    }

    /**
     * Tests the normal behaviour of the {@link IdentityHashMap#put(Object, Object)}
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
     *         0 <= i < \old(table.length) / 2;
     *         \old(table[i*2]) == maskNull(key))
     *         ==> size == \old(size) && modCount == \old(modCount) &&
     *         (\forall int j;
     *             0 <= j < \old(table.length) - 1 && j % 2 == 0;
     *             \old(table[j]) == maskNull(key) ==> \result == \old(table[j + 1]))) &&
     *
     *     // If the key does not exist, size must me increased by 1, modCount must change,
     *     // and null must be returned
     *     (!(\exists int i;
     *         0 <= i < \old(table.length) - 1;
     *         i % 2 == 0 && \old(table[i]) == maskNull(key))
     *         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == null) &&
     *
     *     // If the key does not exist, and \old(size) + 1) >= \old(threshold),
     *     // table must be resized
     *     (!(\exists \bigint i;
     *         0 <= i < \old(table.length) - 1;
     *         i % 2 == 0 && \old(table[i]) == maskNull(key)) &&
     *         \old(size) + 1 >= \old(threshold))
     *         ==>
     *         ((\old(table.length) == 2 * MAXIMUM_CAPACITY) ==>
     *            (threshold == MAXIMUM_CAPACITY - 1 && table.length == \old(table.length)) &&
     *          (\old(table.length) < 2 * MAXIMUM_CAPACITY) ==>
     *            (threshold == table.length / 3 && table.length == \old(table.length) * 2)) &&
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
     *         \old(table[i-1]) != maskNull(key) ==>
     *             (\exists int j;
     *                 0 < j < table.length;
     *                 j % 2 == 1 && \old(table[i]) == table[j])) &&
     *
     *     // After execution, the table contains the new key associated with the new value
     *     (\exists int i;
     *         0 <= i < table.length - 1 ;
     *         i % 2 == 0 && table[i] == maskNull(key) && table[i + 1] == value);
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

        // If the key does not exist, and \old(size) + 1) >= \old(threshold),
        // table must be resized
        testIfTableIsResizedWhenResizeIsRequired();

        // Test the assignability
        assertAssignableClause(map, "put", new String[]{"k", "v"}, new String[]{"size", "table", "threshold", "modCount"});

        // Test the class invariants (postcondition)
        assertClassInvariants(map);
    }

    // When key already exists ... overwrite old element
    // This test uses null for a key, so we also test the maskNull(key) spec.
    private void testPutWhenKeyAlreadyExists() throws NoSuchFieldException, IllegalAccessException {
        final Object newKey = null; // Note: using null as key to test maskNull()
        final int oldSize = map.size();
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Map<Object, Object> oldEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        final Object oldValue = map.get(newKey);
        assertThat(map.put(newKey, "newValue"), is(oldValue));
        assertThat(map.size(), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));

        // Make sure the new element (still) exists
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        boolean found = false;
        for (int i = 0; i < table.length; i++) {
            if (maskedNullKey.equals(table[i])) { // Note: using maskedNullKey to search in table
                assertThat((String)table[i+1], is("newValue"));
                found = true;
                break;
            }
        }
        assertThat(found, is(true));

        final Map<Object, Object> newEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        // After execution, all old keys are still present
        assertThat(newEntriesAsMap.keySet().containsAll(oldEntriesAsMap.keySet()), is(true));
        // After execution, all old values, not identified by the new key, are still present
        oldEntriesAsMap.remove(newKey);
        assertThat(newEntriesAsMap.values().containsAll(oldEntriesAsMap.values()), is(true));
    }

    // When key does not yet exists ... element should be added, and null should be returned
    private void testPutWhenKeyDoesNotYetExist()
            throws NoSuchFieldException, IllegalAccessException {
        final int oldSize = map.size();
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Map<Object, Object> oldEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));

        // If the key did not already exist, the return value must be null, size must be increased, and modCount
        // must be changed
        boolean found;
        Object[] table;
        final String newKey = "newKey";
        assertThat(map.put(newKey, "otherNewValue"), nullValue());
        assertThat(map.size(), is(oldSize + 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(oldModCount));

        // Make sure the new element exists, and is associated with the new value
        table = (Object[]) getValueByFieldName(map, "table");
        found = false;
        for (int i = 0; i < table.length; i++) {
            if (newKey.equals(table[i])) {
                assertThat((String)table[i+1], is("otherNewValue"));
                found = true;
                break;
            }
        }
        assertThat(found, is(true));

        final Map<Object, Object> newEntriesAsMap = getEntriesAsMap((Object[])getValueByFieldName(map, "table"));
        // After execution, all old keys are still present
        assertThat(newEntriesAsMap.keySet().containsAll(oldEntriesAsMap.keySet()), is(true));
        // After execution, all old values are still present
        assertThat(newEntriesAsMap.values().containsAll(oldEntriesAsMap.values()), is(true));
    }

    // If the key does not exist, and \old(size) + 1) >= \old(threshold),
    // table must be resized
    // JML:
    //   (!(\exists \bigint i;
    //     0 <= i < \old(table.length) - 1;
    //     i % 2 == 0 && \old(table[i]) == maskNull(key)) &&
    //     \old(size) + 1 >= \old(threshold))
    //     ==>
    //     ((\old(table.length) == 2 * MAXIMUM_CAPACITY) ==>
    //        (threshold == MAXIMUM_CAPACITY - 1 && table.length == \old(table.length)) &&
    //      (\old(table.length) < 2 * MAXIMUM_CAPACITY) ==>
    //        (threshold == table.length / 3 && table.length == \old(table.length) * 2));
    private void testIfTableIsResizedWhenResizeIsRequired()
            throws NoSuchFieldException, IllegalAccessException {
        final int oldSize = map.size();
        final int oldLength = ((Object[]) getValueByFieldName(map, "table")).length;
        final int maxCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");

        // This should trigger a resize
        setValueByFieldName(map, "threshold", oldSize + 1);

        final String newKey = "brandNewKey";
        assertThat(map.put(newKey, "otherBrandNewValue"), nullValue());
        assertThat(map.size(), is(oldSize + 1));
        final int newLength = ((Object[]) getValueByFieldName(map, "table")).length;
        final int newThreshold = (int) getValueByFieldName(map, "threshold");
        if(oldLength == 2 * maxCapacity) {
            assertThat(newLength, is(oldLength));
            assertThat(newThreshold, is(maxCapacity - 1));
        }
        else if(oldLength < 2 * maxCapacity) {
            assertThat(newLength, greaterThan(oldLength));
            assertThat(newThreshold, is(newLength / 3));
        } else {
            throw new AssertionFailedError("Unexpected situation in test testIfTableIsResizedWhenResizeIsRequired.");
        }
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
