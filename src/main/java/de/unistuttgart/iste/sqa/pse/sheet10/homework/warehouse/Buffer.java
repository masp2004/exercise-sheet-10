package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;
import java.util.LinkedList;
import java.util.Queue;

/**
 * Represents a buffer for temporary storage of items.
 *
 * @author Marvin Spiegel
 */
public final class Buffer {

	private Queue<StationeryItem> itemQueue;

	/*@
	@ ensures itemQueue != null;
	@*/
	/**
	 * Creates a new buffer.
	 */
	public Buffer() {
		itemQueue = new LinkedList<>();
	}

	/*@
	@ requires stationeryItem != null;
	@ ensures itemQueue.size() == \old(itemQueue.size()) + 1;
	@*/
	/**
	 * Adds an item to the buffer.
	 */
	public void bufferItem(final StationeryItem stationeryItem) {
		itemQueue.add(stationeryItem);
	}

	/*@
	@ requires !isEmpty();
	@ ensures \result != null;
	@*/
	/**
	 * Returns the next item in the buffer.
	 */
	public StationeryItem releaseItem() {
		if (isEmpty()) {
			throw new IllegalStateException("Buffer is empty. Cannot release item.");
		}
		return itemQueue.poll();
	}

	/*@
	@ ensures \result == itemQueue.isEmpty();
	@*/
	/**
	 * Returns true if the buffer is empty.
	 */
	public /*@ pure @*/ boolean isEmpty() {
		return itemQueue.isEmpty();
	}
}
