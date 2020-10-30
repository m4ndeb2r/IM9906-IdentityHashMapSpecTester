package nl.ou.im9906;

import org.junit.Test;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.hash;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#closeDeletion(int)}
 * method.
 */
public class IdentityHashMapCloseDeletionTest {

    private static final boolean VERBOSE = false;

    /**
     * Tests the class invariant after deleting an element with the same hash (index) as another
     * element. The class invariant checks the proper workings of closeDeletion.
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void removeElementWithIdenticalHash()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchClassException {
        int runs = 1000;
        for (int i = 0; i < runs; i++) {
            doAddAndremoveElementsWithIdenticalHash(i * 1000, 40 * i + 10, 4 * i);
        }
    }

    private void doAddAndremoveElementsWithIdenticalHash(int attempts, int maxElements, int initialTableSize)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchClassException {
        final IdentityHashMap<String, String> map = new IdentityHashMap<>(initialTableSize);
        assertClassInvariants(map);

        final List<String> keys = new ArrayList<>();
        int firstHash = -1;

        for(int i = 0; i < attempts; i++) {
            final Object[] table = (Object[])getValueByFieldName(map, "table");
            final String newKey = new String("K");
            final int hash = hash(newKey, table.length);
            if (firstHash < 0) firstHash = hash;
            if (firstHash == hash) {
                map.put(newKey, String.format("Original hash: %d", hash));
                keys.add(newKey);
            }
            if (map.size() >= maxElements) break; // Performance+
        }
        assertClassInvariants(map);

        if (map.size() > 3) {
            int idx = keys.size() / 2;
            if (VERBOSE) {
                System.out.println(String.format("Map contains %d elements with hash (index) %d", keys.size(), firstHash));
                System.out.println(String.format("Removing %dth element ", idx));
            }
            map.remove(keys.get(idx));
        }
        assertClassInvariants(map);
    }
}
