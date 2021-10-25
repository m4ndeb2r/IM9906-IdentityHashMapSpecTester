package nl.ou.im9906;

import junit.framework.AssertionFailedError;
import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.getValueByStaticFieldName;
import static org.junit.Assert.fail;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#put(Object, Object)}
 * method in relation to a possible bug.
 */
public class IdentityHashMapPutExceptionTest {

    private SmallIdentityHashMapForPutException<String, String> map;

    @Test
    public void testConstructorWithMapContainingMaxCapacityOfElements()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {

        final int maxCapacity = (int) getValueByStaticFieldName(SmallIdentityHashMapForPutException.class, "MAXIMUM_CAPACITY");
        map = new SmallIdentityHashMapForPutException<String, String>();

        // Add MAXIMUM_CAPACIY - 2 unique elements to the map
        for (int i = 0; i < maxCapacity - 2; i++) {
            map.put(new String("key_" + (i + 1)), new String("value_" + (i + 1)));
        }

        // At this point, there are two empty entries. The class invariant still holds
        assertClassInvariants(map);

        // Now, keep adding entries, and ignore the IllegalStateExceptions thrown by resize().
        // The class invariant will be violated, and the put method will subsequently loop infinitely.
        for (int j = 0; j < 5; j++) {
            // Print the state beforehand
            System.out.println("");
            printState(map);
            System.out.println("Executing put(key_" + (map.size() + 1) + ", value_" + (map.size() + 1) + ") ....");

            // Try to put an entry into the map
            try {
                map.put("key_" + map.size() + 1, "value_" + map.size() + 1);
                fail("No exception was thrown. This was not expected.");
            } catch (IllegalStateException e) {
                System.out.println("IllegalStateException occurred as expected (via resize).");
            }

            // Print the state afterwards
            printState(map);
        }
    }

    private void printState(SmallIdentityHashMapForPutException<String, String> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final int maxCapacity = (int) getValueByStaticFieldName(SmallIdentityHashMapForPutException.class, "MAXIMUM_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        final int threshold = (int) getValueByFieldName(map, "threshold");
        boolean isClassInvariantViolated = false;
        try {
            assertClassInvariants(map);
        } catch (AssertionError e) {
            isClassInvariantViolated = true;
        }

        System.out.println("Current state of " + map.getClass().getSimpleName());
        System.out.println("- size = " + map.size());
        System.out.println("- table.length = " + table.length);
        System.out.println("- threshold = " + threshold);
        System.out.println("- max capacity = " + maxCapacity);
        System.out.println("- number of empty entries = " + emptyEntries(table));
        if (isClassInvariantViolated) {
            System.out.println("- class invariant is violated!!!");
        } else {
            System.out.println("- class invariant holds");
        }

    }

    private int emptyEntries(Object[] table)
            throws NoSuchFieldException, IllegalAccessException {
        int count = 0;
        for (int i = 0; i < table.length; i += 2) {
            if (table[i] == null) count++;
        }
        return count;
    }

}
