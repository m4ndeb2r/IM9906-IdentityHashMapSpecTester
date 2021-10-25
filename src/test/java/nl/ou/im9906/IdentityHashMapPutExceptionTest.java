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
import static nl.ou.im9906.ReflectionUtils.getValueByStaticFieldName;
import static nl.ou.im9906.ReflectionUtils.setValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

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
        final Map<String, String> constructorInputMap = new HashMap<String, String>();
        for (int i = 0; i < maxCapacity - 2; i++) {
            constructorInputMap.put("key_" + i, "value_" + i);
        }
        map = new SmallIdentityHashMapForPutException<String, String>(constructorInputMap);

        for (int j = 0; j < 5; j++) {
            try {
                System.out.println("Size voor put: " + map.size());
                System.out.println("Put .....");
                map.put(new String("BOOM! BOOM!"), "Out go the lights!");
                System.out.println("Geen exception.");
                System.out.println("=====================================");
            } catch (IllegalStateException e) {
                System.out.println("Boem!");
                System.out.println("Size na mislukte put: " + map.size());
                System.out.println("=====================================");

                // Test the class invariant if exception has occurred
                assertClassInvariants(map);
            }
        }

    }

}
