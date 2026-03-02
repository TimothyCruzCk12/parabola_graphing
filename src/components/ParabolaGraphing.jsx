import React, { useState, useRef, useCallback, useEffect } from 'react';
import '../glow.css';

const WIDTH = 500;
const HEIGHT = 500;
const MIN = -10;
const MAX = 10;
/** One full segment past MIN/MAX so arrows sit one unit beyond the last tick */
const EXTENDED_MIN = MIN - 1;
const EXTENDED_MAX = MAX + 1;
const PADDING = 40;
const centerX = WIDTH / 2;
const centerY = HEIGHT / 2;
const plotWidth = WIDTH - 2 * PADDING;
const plotHeight = HEIGHT - 2 * PADDING;
const scaleX = plotWidth / (MAX - MIN);
const scaleY = plotHeight / (MAX - MIN);

/** Map value x in [MIN, MAX] to SVG x */
const valueToX = (x) => centerX + x * scaleX;
/** Map value y in [MIN, MAX] to SVG y (SVG y increases downward) */
const valueToY = (y) => centerY - y * scaleY;
/** Map SVG x to value */
const xToValue = (px) => (px - centerX) / scaleX;
/** Map SVG y to value */
const yToValue = (py) => (centerY - py) / scaleY;

/** Clamp value to [MIN, MAX] */
const clamp = (v) => Math.max(MIN, Math.min(MAX, v));
/** Clamp value to extended bounds (so parabola stays in container) */
const clampExtended = (v) => Math.max(EXTENDED_MIN, Math.min(EXTENDED_MAX, v));
/** Clamp y to container vertical bounds so parabola stays on screen. */
const clampContainerY = (v) => Math.max(containerMinY, Math.min(containerMaxY, v));
/** Round value to nearest integer and clamp */
const roundToTick = (v) => Math.round(clamp(v));

const GRID_CELL = scaleX; // 1 unit
const POINT_RADIUS = 6;
const PARABOLA_ARROW_SIZE = 8;
const PARABOLA_ANIMATION_DURATION_MS = 1500;
const MAX_PARABOLAS = 2; // max visible; when a third is drawn, oldest is dropped after it animates (like TwoPointDrawing MAX_LINES)
/** Minimum horizontal distance from vertex to define parabola (avoid degenerate a) */
const MIN_DX = 0.5;
/** Number of samples for parabola path */
const PARABOLA_SAMPLES = 300;

const tickValues = Array.from({ length: MAX - MIN + 1 }, (_, i) => MIN + i);

/** Container bounds in SVG pixel space (full graph area). */
const CONTAINER_LEFT = 0;
const CONTAINER_TOP = 0;
const CONTAINER_RIGHT = WIDTH;
const CONTAINER_BOTTOM = HEIGHT;
/** Value-space bounds that map to container edges (so parabola reaches SVG edges like TwoPointDrawing line). */
const containerMinX = (CONTAINER_LEFT - centerX) / scaleX;
const containerMaxX = (CONTAINER_RIGHT - centerX) / scaleX;
const containerMinY = (centerY - CONTAINER_BOTTOM) / scaleY;
const containerMaxY = (centerY - CONTAINER_TOP) / scaleY;

/** Arrow polygon points (SVG): tip at (sx,sy), direction (dx,dy) normalized, size in px. */
function arrowPoints(sx, sy, dx, dy, size) {
	const half = size / 2;
	const baseX = sx - size * dx;
	const baseY = sy - size * dy;
	const perpX = -dy;
	const perpY = dx;
	return `${sx},${sy} ${baseX + half * perpX},${baseY + half * perpY} ${baseX - half * perpX},${baseY - half * perpY}`;
}

/** Compute arrow direction in SVG from value-space tangent (vx, vy) pointing outward (left or right). */
function arrowDirFromTangent(vx, vy) {
	const len = Math.hypot(vx, vy) || 1;
	const dx = (vx / len) * scaleX;
	const dy = -(vy / len) * scaleY;
	const lenSvg = Math.hypot(dx, dy) || 1;
	return { dx: dx / lenSvg, dy: dy / lenSvg };
}

/**
 * Build parabola path and arrow data. Path stops at container top/bottom (no flat edge);
 * arrow is placed exactly at the stop point with correct tangent direction.
 */
function parabolaPathAndArrows(h, k, a) {
	const xMin = containerMinX;
	const xMax = containerMaxX;
	const dx = (xMax - xMin) / (PARABOLA_SAMPLES - 1);
	// Left half: vertex → left; stop at top/bottom boundary with intersection point (no flattening)
	const nLeft = Math.max(2, Math.round((h - xMin) / dx));
	const stepLeft = (nLeft > 1) ? (h - xMin) / (nLeft - 1) : 0;
	let pathDLeft = '';
	let leftEndpoint = null; // { sx, sy, xVal, yVal } for arrow at actual stop
	for (let i = 0; i < nLeft; i++) {
		const x = h - i * stepLeft;
		const y = a * (x - h) * (x - h) + k;
		if (y > containerMaxY) {
			const diff = (containerMaxY - k) / a;
			if (diff >= 0) {
				const xCross = h - Math.sqrt(diff);
				const sxCross = valueToX(xCross);
				const syCross = valueToY(containerMaxY);
				if (pathDLeft === '') pathDLeft = `M ${sxCross} ${syCross}`;
				else pathDLeft += ` L ${sxCross} ${syCross}`;
				leftEndpoint = { sx: sxCross, sy: syCross, xVal: xCross, yVal: containerMaxY };
			}
			break;
		}
		if (y < containerMinY) {
			const diff = (containerMinY - k) / a;
			if (diff >= 0) {
				const xCross = h - Math.sqrt(diff);
				const sxCross = valueToX(xCross);
				const syCross = valueToY(containerMinY);
				if (pathDLeft === '') pathDLeft = `M ${sxCross} ${syCross}`;
				else pathDLeft += ` L ${sxCross} ${syCross}`;
				leftEndpoint = { sx: sxCross, sy: syCross, xVal: xCross, yVal: containerMinY };
			}
			break;
		}
		const sx = valueToX(x);
		const sy = valueToY(y);
		if (pathDLeft === '') pathDLeft = `M ${sx} ${sy}`;
		else pathDLeft += ` L ${sx} ${sy}`;
		leftEndpoint = { sx, sy, xVal: x, yVal: y };
	}
	// Right half: vertex → right; stop at top/bottom boundary
	const nRight = Math.max(2, Math.round((xMax - h) / dx));
	const stepRight = (nRight > 1) ? (xMax - h) / (nRight - 1) : 0;
	let pathDRight = '';
	let rightEndpoint = null;
	for (let i = 0; i < nRight; i++) {
		const x = h + i * stepRight;
		const y = a * (x - h) * (x - h) + k;
		if (y > containerMaxY) {
			const diff = (containerMaxY - k) / a;
			if (diff >= 0) {
				const xCross = h + Math.sqrt(diff);
				const sxCross = valueToX(xCross);
				const syCross = valueToY(containerMaxY);
				if (pathDRight === '') pathDRight = `M ${sxCross} ${syCross}`;
				else pathDRight += ` L ${sxCross} ${syCross}`;
				rightEndpoint = { sx: sxCross, sy: syCross, xVal: xCross, yVal: containerMaxY };
			}
			break;
		}
		if (y < containerMinY) {
			const diff = (containerMinY - k) / a;
			if (diff >= 0) {
				const xCross = h + Math.sqrt(diff);
				const sxCross = valueToX(xCross);
				const syCross = valueToY(containerMinY);
				if (pathDRight === '') pathDRight = `M ${sxCross} ${syCross}`;
				else pathDRight += ` L ${sxCross} ${syCross}`;
				rightEndpoint = { sx: sxCross, sy: syCross, xVal: xCross, yVal: containerMinY };
			}
			break;
		}
		const sx = valueToX(x);
		const sy = valueToY(y);
		if (pathDRight === '') pathDRight = `M ${sx} ${sy}`;
		else pathDRight += ` L ${sx} ${sy}`;
		rightEndpoint = { sx, sy, xVal: x, yVal: y };
	}
	// Full path for ghost: same stop-at-boundary logic, built left-to-right (two segments if it exits and re-enters)
	const pathDParts = [];
	let inSegment = false;
	let lastSx = 0, lastSy = 0;
	for (let i = 0; i < PARABOLA_SAMPLES; i++) {
		const x = xMin + i * dx;
		const y = a * (x - h) * (x - h) + k;
		const sx = valueToX(x);
		const sy = valueToY(y);
		if (y >= containerMinY && y <= containerMaxY) {
			if (!inSegment) {
				pathDParts.push(`M ${sx} ${sy}`);
				inSegment = true;
			} else pathDParts[pathDParts.length - 1] += ` L ${sx} ${sy}`;
			lastSx = sx;
			lastSy = sy;
		} else {
			if (inSegment) {
				const yBound = y > containerMaxY ? containerMaxY : containerMinY;
				const diff = (yBound - k) / a;
				if (diff >= 0) {
					const xCross = x > h ? h + Math.sqrt(diff) : h - Math.sqrt(diff);
					const sxCross = valueToX(xCross);
					const syCross = valueToY(yBound);
					pathDParts[pathDParts.length - 1] += ` L ${sxCross} ${syCross}`;
				}
				inSegment = false;
			}
		}
	}
	const pathD = pathDParts.length ? pathDParts.join(' ') : '';

	// Arrows at actual endpoints (on edge or at top/bottom stop)
	const leftDir = leftEndpoint
		? arrowDirFromTangent(-1, -2 * a * (leftEndpoint.xVal - h))
		: { dx: -1, dy: 0 };
	const rightDir = rightEndpoint
		? arrowDirFromTangent(1, 2 * a * (rightEndpoint.xVal - h))
		: { dx: 1, dy: 0 };
	return {
		pathD,
		pathDLeft,
		pathDRight,
		leftArrow: leftEndpoint
			? { sx: leftEndpoint.sx, sy: leftEndpoint.sy, dx: leftDir.dx, dy: leftDir.dy }
			: { sx: valueToX(xMin), sy: centerY, dx: -1, dy: 0 },
		rightArrow: rightEndpoint
			? { sx: rightEndpoint.sx, sy: rightEndpoint.sy, dx: rightDir.dx, dy: rightDir.dy }
			: { sx: valueToX(xMax), sy: centerY, dx: 1, dy: 0 },
	};
}

const ParabolaGraphing = () => {
	const [hoverPreview, setHoverPreview] = useState(null); // { x, y } in value space, or null
	const [pointsHistory, setPointsHistory] = useState([]); // all points (for undo/redo: undone points stay in array)
	const [historyIndex, setHistoryIndex] = useState(0); // how many points are "current" (undo/redo is point-by-point)
	const [parabolaProgress, setParabolaProgress] = useState(0); // 0..1 for draw animation
	const [animatingParabolaIndex, setAnimatingParabolaIndex] = useState(null); // which parabola (0-based) is animating, or null
	const [showGlow, setShowGlow] = useState(true);
	const containerRef = useRef(null);

	// Current points = those before historyIndex (undo/redo moves this boundary)
	const currentPoints = pointsHistory.slice(0, historyIndex);
	const numParabolas = Math.floor(historyIndex / 2);

	// Build parabola data from point pairs; then take last MAX_PARABOLAS for display
	const allParabolasData = [];
	for (let i = 0; i < numParabolas; i++) {
		const vertex = currentPoints[2 * i];
		const secondPoint = currentPoints[2 * i + 1];
		const h = vertex.x;
		const k = vertex.y;
		const denom = (secondPoint.x - h) * (secondPoint.x - h);
		if (denom >= MIN_DX * MIN_DX) {
			const a = (secondPoint.y - k) / denom;
			allParabolasData.push({ h, k, a, vertex, secondPoint, index: i });
		}
	}
	// Visible: at most MAX_PARABOLAS. While animating, show one fewer "full" and draw the animating one with progress.
	const isAnimating = animatingParabolaIndex !== null;
	const visibleParabolasFull = isAnimating
		? allParabolasData.filter((p) => p.index !== animatingParabolaIndex).slice(-(MAX_PARABOLAS - 1))
		: allParabolasData.slice(-MAX_PARABOLAS);
	const animatingParabolaData =
		animatingParabolaIndex != null && allParabolasData[animatingParabolaIndex]
			? allParabolasData[animatingParabolaIndex]
			: null;

	// Point indices that belong to visible parabolas only (so oldest parabola's points are hidden when we have 3+)
	const visibleParabolaStart = Math.max(0, numParabolas - MAX_PARABOLAS);
	const visiblePointStartIndex = 2 * visibleParabolaStart;

	// When a parabola starts animating, run the progress animation
	useEffect(() => {
		if (animatingParabolaIndex == null) return;
		setParabolaProgress(0);
		const start = performance.now();
		const tick = (now) => {
			const elapsed = now - start;
			const progress = Math.min(1, elapsed / PARABOLA_ANIMATION_DURATION_MS);
			setParabolaProgress(progress);
			if (progress < 1) {
				requestAnimationFrame(tick);
			} else {
				setAnimatingParabolaIndex(null);
				setParabolaProgress(1);
			}
		};
		const id = requestAnimationFrame(tick);
		return () => cancelAnimationFrame(id);
	}, [animatingParabolaIndex]);

	const clientToSvg = useCallback((clientX, clientY) => {
		const el = containerRef.current;
		if (!el) return null;
		const rect = el.getBoundingClientRect();
		const x = clientX - rect.left;
		const y = clientY - rect.top;
		return {
			x: Math.max(0, Math.min(WIDTH, x)),
			y: Math.max(0, Math.min(HEIGHT, y)),
		};
	}, []);

	const handleClick = useCallback(
		(e) => {
			if (animatingParabolaIndex !== null) return; // ignore clicks while animating (like TwoPointDrawing)
			const pt = clientToSvg(e.clientX, e.clientY);
			if (!pt) return;
			const vx = roundToTick(xToValue(pt.x));
			const vy = roundToTick(yToValue(pt.y));
			const valuePoint = { x: vx, y: vy };

			const nextIndex = historyIndex + 1;
			setPointsHistory((prev) => [...prev.slice(0, historyIndex), valuePoint]);
			setHistoryIndex(nextIndex);
			// If we just completed a parabola (even number of points >= 2), start its animation
			if (nextIndex >= 2 && nextIndex % 2 === 0) {
				setAnimatingParabolaIndex(nextIndex / 2 - 1);
			}
		},
		[clientToSvg, historyIndex, animatingParabolaIndex]
	);

	const handleMouseMove = useCallback(
		(e) => {
			const pt = clientToSvg(e.clientX, e.clientY);
			if (!pt) {
				setHoverPreview(null);
				return;
			}
			setHoverPreview({
				x: roundToTick(xToValue(pt.x)),
				y: roundToTick(yToValue(pt.y)),
			});
		},
		[clientToSvg]
	);

	const handleMouseLeave = useCallback(() => {
		setHoverPreview(null);
	}, []);

	const canUndo = historyIndex > 0;
	const canRedo = historyIndex < pointsHistory.length;
	const canReset = pointsHistory.length > 0;

	// Ghost parabola: when we have an odd number of points (vertex placed, no second yet), preview from hover
	const vertexForGhost = historyIndex > 0 && historyIndex % 2 === 1 ? currentPoints[historyIndex - 1] : null;
	let ghostParabolaData = null;
	if (vertexForGhost && hoverPreview) {
		const h = vertexForGhost.x;
		const k = vertexForGhost.y;
		const denom = (hoverPreview.x - h) * (hoverPreview.x - h);
		if (denom >= MIN_DX * MIN_DX) {
			const a = (hoverPreview.y - k) / denom;
			ghostParabolaData = parabolaPathAndArrows(h, k, a);
		}
	}

	// Axis line endpoints: extend one segment past MIN/MAX (arrows at extended ends)
	const arrowSize = 10;
	const arrowHeight = 7;
	const xMin = valueToX(EXTENDED_MIN);
	const xMax = valueToX(EXTENDED_MAX);
	const yMin = valueToY(EXTENDED_MIN);
	const yMax = valueToY(EXTENDED_MAX);
	const xAxisLeft = xMin + arrowSize;
	const xAxisRight = xMax - arrowSize;
	const yAxisTop = yMax + arrowSize;
	const yAxisBottom = yMin - arrowSize;

	return (
		<div
			ref={containerRef}
			className="parabola-graphing"
			role="application"
			aria-label="Parabola graphing coordinate plane"
			tabIndex={0}
			onClick={handleClick}
			onMouseMove={handleMouseMove}
			onMouseLeave={handleMouseLeave}
			style={{
				position: 'relative',
				width: WIDTH,
				height: HEIGHT,
				border: '1px solid #ccc',
				borderRadius: 4,
				overflow: 'hidden',
				backgroundColor: '#fff',
				cursor: 'crosshair',
				userSelect: 'none',
				WebkitUserSelect: 'none',
				MozUserSelect: 'none',
				msUserSelect: 'none',
			}}
		>
			{/* Undo, Redo, Reset — same layout as TwoPointDrawing */}
			<div
				className={`segmented-glow-button simple-glow compact${!showGlow ? ' hide-orbit' : ''}`}
				style={{ position: 'absolute', top: 11, right: 12, zIndex: 1 }}
			>
				<div className="segment-container">
					<button
						type="button"
						className={`segment ${!canUndo ? 'inactive' : ''}`}
						onClick={(e) => {
							e.stopPropagation();
							if (!canUndo) return;
							setShowGlow(false);
							setHistoryIndex((i) => Math.max(0, i - 1));
							// If we undid the second point of the animating parabola, cancel animation
							if (animatingParabolaIndex !== null && historyIndex === 2 * (animatingParabolaIndex + 1)) {
								setAnimatingParabolaIndex(null);
								setParabolaProgress(0);
							}
						}}
						disabled={!canUndo}
					>
						Undo
					</button>
					<button
						type="button"
						className={`segment ${!canRedo ? 'inactive' : ''}`}
						onClick={(e) => {
							e.stopPropagation();
							if (!canRedo) return;
							setShowGlow(false);
							setHistoryIndex((i) => Math.min(pointsHistory.length, i + 1));
						}}
						disabled={!canRedo}
					>
						Redo
					</button>
					<button
						type="button"
						className={`segment ${!canReset ? 'inactive' : ''}`}
						onClick={(e) => {
							e.stopPropagation();
							if (canReset) setShowGlow(false);
							setPointsHistory([]);
							setHistoryIndex(0);
							setParabolaProgress(0);
							setAnimatingParabolaIndex(null);
						}}
						disabled={!canReset}
					>
						Reset
					</button>
				</div>
			</div>
			<svg width={WIDTH} height={HEIGHT} style={{ display: 'block', pointerEvents: 'none' }}>
				<defs>
					<pattern
						id="grid-parabola"
						x={PADDING}
						y={PADDING}
						width={GRID_CELL}
						height={GRID_CELL}
						patternUnits="userSpaceOnUse"
					>
						<path
							d={`M 0 0 L 0 ${GRID_CELL} M 0 0 L ${GRID_CELL} 0 M ${GRID_CELL} 0 L ${GRID_CELL} ${GRID_CELL} M 0 ${GRID_CELL} L ${GRID_CELL} ${GRID_CELL}`}
							stroke="#e6e6e6"
							strokeWidth="1"
							fill="none"
						/>
					</pattern>
					<clipPath id="plot-clip-parabola">
						<rect x={CONTAINER_LEFT} y={CONTAINER_TOP} width={CONTAINER_RIGHT} height={CONTAINER_BOTTOM} />
					</clipPath>
				</defs>
				<rect width={WIDTH} height={HEIGHT} fill="url(#grid-parabola)" />
				{/* X axis */}
				<line
					x1={xAxisLeft}
					y1={centerY}
					x2={xAxisRight}
					y2={centerY}
					stroke="#999999"
					strokeWidth={2}
				/>
				{/* Y axis */}
				<line
					x1={centerX}
					y1={yAxisTop}
					x2={centerX}
					y2={yAxisBottom}
					stroke="#999999"
					strokeWidth={2}
				/>
				{/* Axis labels */}
				<text
					x={valueToX(10)}
					y={centerY - 12}
					textAnchor="middle"
					fontSize="14px"
					fontWeight="bold"
					fontStyle="italic"
					fill="#999999"
					fontFamily="'Latin Modern Roman CK12', 'Latin Modern Roman', serif"
				>
					x-axis
				</text>
				<text
					x={centerX + 14}
					y={yMax + 5}
					textAnchor="start"
					dominantBaseline="middle"
					fontSize="14px"
					fontWeight="bold"
					fontStyle="italic"
					fill="#999999"
					fontFamily="'Latin Modern Roman CK12', 'Latin Modern Roman', serif"
				>
					y-axis
				</text>
				{/* X axis ticks and labels */}
				{tickValues.map((value) => {
					const x = valueToX(value);
					return (
						<g key={`x-${value}`}>
							<line
								x1={x}
								y1={centerY}
								x2={x}
								y2={centerY + 10}
								stroke="#999999"
								strokeWidth={1.5}
							/>
							{value !== 0 && (
								<text
									x={x}
									y={centerY + 26}
									textAnchor="middle"
									fontSize="14px"
									fontWeight="bold"
									fill="#999999"
									fontFamily="'Latin Modern Roman CK12', 'Latin Modern Roman', serif"
								>
									{value}
								</text>
							)}
						</g>
					);
				})}
				{/* Y axis ticks and labels */}
				{tickValues.map((value) => {
					const y = valueToY(value);
					return (
						<g key={`y-${value}`}>
							<line
								x1={centerX}
								y1={y}
								x2={centerX - 10}
								y2={y}
								stroke="#999999"
								strokeWidth={1.5}
							/>
							{value !== 0 && (
								<text
									x={centerX - 14}
									y={y + 5}
									textAnchor="end"
									fontSize="14px"
									fontWeight="bold"
									fill="#999999"
									fontFamily="'Latin Modern Roman CK12', 'Latin Modern Roman', serif"
								>
									{value}
								</text>
							)}
						</g>
					);
				})}
				{/* Arrows at all 4 ends: right (+x), left (-x), top (+y), bottom (-y) */}
				<polygon
					points={`${xMax - arrowSize},${centerY - arrowHeight} ${xMax},${centerY} ${xMax - arrowSize},${centerY + arrowHeight}`}
					fill="#999999"
				/>
				<polygon
					points={`${xMin + arrowSize},${centerY - arrowHeight} ${xMin},${centerY} ${xMin + arrowSize},${centerY + arrowHeight}`}
					fill="#999999"
				/>
				<polygon
					points={`${centerX - arrowHeight},${yMax + arrowSize} ${centerX},${yMax} ${centerX + arrowHeight},${yMax + arrowSize}`}
					fill="#999999"
				/>
				<polygon
					points={`${centerX - arrowHeight},${yMin - arrowSize} ${centerX},${yMin} ${centerX + arrowHeight},${yMin - arrowSize}`}
					fill="#999999"
				/>
				{/* Visible parabolas (full, not animating) with their vertex and second point */}
				{visibleParabolasFull.map(({ h, k, a, vertex, secondPoint }, idx) => {
					const data = parabolaPathAndArrows(h, k, a);
					return (
						<g key={idx} clipPath="url(#plot-clip-parabola)">
							<path
								d={data.pathDLeft}
								fill="none"
								stroke="#1967d2"
								strokeWidth={3}
								strokeLinecap="round"
								strokeLinejoin="round"
							/>
							<path
								d={data.pathDRight}
								fill="none"
								stroke="#1967d2"
								strokeWidth={3}
								strokeLinecap="round"
								strokeLinejoin="round"
							/>
							<polygon
								points={arrowPoints(
									data.leftArrow.sx,
									data.leftArrow.sy,
									data.leftArrow.dx,
									data.leftArrow.dy,
									PARABOLA_ARROW_SIZE
								)}
								fill="#1967d2"
							/>
							<polygon
								points={arrowPoints(
									data.rightArrow.sx,
									data.rightArrow.sy,
									data.rightArrow.dx,
									data.rightArrow.dy,
									PARABOLA_ARROW_SIZE
								)}
								fill="#1967d2"
							/>
							{/* Vertex and second point remain visible */}
							{vertex && (
								<circle
									cx={valueToX(vertex.x)}
									cy={valueToY(vertex.y)}
									r={POINT_RADIUS}
									fill="#1967d2"
									stroke="#fff"
									strokeWidth={2}
								/>
							)}
							{secondPoint && (
								<circle
									cx={valueToX(secondPoint.x)}
									cy={valueToY(secondPoint.y)}
									r={POINT_RADIUS}
									fill="#1967d2"
									stroke="#fff"
									strokeWidth={2}
								/>
							)}
						</g>
					);
				})}
				{/* Ghost parabola: preview when vertex is placed and mouse is hovering */}
				{ghostParabolaData && (
					<g clipPath="url(#plot-clip-parabola)">
						<path
							d={ghostParabolaData.pathD}
							fill="none"
							stroke="#1967d2"
							strokeWidth={2.5}
							strokeOpacity={0.5}
							strokeDasharray="8 6"
							strokeLinecap="round"
							strokeLinejoin="round"
						/>
						<polygon
							points={arrowPoints(
								ghostParabolaData.leftArrow.sx,
								ghostParabolaData.leftArrow.sy,
								ghostParabolaData.leftArrow.dx,
								ghostParabolaData.leftArrow.dy,
								PARABOLA_ARROW_SIZE
							)}
							fill="#1967d2"
							fillOpacity={0.5}
						/>
						<polygon
							points={arrowPoints(
								ghostParabolaData.rightArrow.sx,
								ghostParabolaData.rightArrow.sy,
								ghostParabolaData.rightArrow.dx,
								ghostParabolaData.rightArrow.dy,
								PARABOLA_ARROW_SIZE
							)}
							fill="#1967d2"
							fillOpacity={0.5}
						/>
					</g>
				)}
				{/* Parabola currently animating (vertex expanding to both sides, then arrows) */}
				{animatingParabolaData && (() => {
					const data = parabolaPathAndArrows(animatingParabolaData.h, animatingParabolaData.k, animatingParabolaData.a);
					return (
						<g clipPath="url(#plot-clip-parabola)">
							<path
								d={data.pathDLeft}
								pathLength={1}
								strokeDasharray={1}
								strokeDashoffset={1 - parabolaProgress}
								fill="none"
								stroke="#1967d2"
								strokeWidth={3}
								strokeLinecap="round"
								strokeLinejoin="round"
							/>
							<path
								d={data.pathDRight}
								pathLength={1}
								strokeDasharray={1}
								strokeDashoffset={1 - parabolaProgress}
								fill="none"
								stroke="#1967d2"
								strokeWidth={3}
								strokeLinecap="round"
								strokeLinejoin="round"
							/>
							{parabolaProgress >= 1 && (
								<>
									<polygon
										points={arrowPoints(
											data.leftArrow.sx,
											data.leftArrow.sy,
											data.leftArrow.dx,
											data.leftArrow.dy,
											PARABOLA_ARROW_SIZE
										)}
										fill="#1967d2"
									/>
									<polygon
										points={arrowPoints(
											data.rightArrow.sx,
											data.rightArrow.sy,
											data.rightArrow.dx,
											data.rightArrow.dy,
											PARABOLA_ARROW_SIZE
										)}
										fill="#1967d2"
									/>
								</>
							)}
						</g>
					);
				})()}
				{/* Points for visible parabolas only (oldest parabola's points hidden when 3+ parabolas) */}
				{currentPoints.slice(visiblePointStartIndex).map((p, i) => {
					const pointIndex = visiblePointStartIndex + i;
					return (
						<circle
							key={pointIndex}
							cx={valueToX(p.x)}
							cy={valueToY(p.y)}
							r={POINT_RADIUS}
							fill="#1967d2"
							stroke="#fff"
							strokeWidth={2}
						/>
					);
				})}
				{/* Hover preview: where the cursor is in value space */}
				{hoverPreview && (
					<circle
						cx={valueToX(hoverPreview.x)}
						cy={valueToY(hoverPreview.y)}
						r={POINT_RADIUS}
						fill="#1967d2"
						fillOpacity={0.4}
						stroke="#1967d2"
						strokeOpacity={0.5}
						strokeWidth={2}
					/>
				)}
			</svg>
		</div>
	);
};

export default ParabolaGraphing;
